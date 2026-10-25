#!/usr/bin/env python3
"""Serial real-TCP checks of the reference server. Python standard library only.

Suites:
  smoke     invalid options, normal load, malformed inputs, three reply
            mutations through a proxy and a receive cutoff, for every mode
  metadata  request metadata limits at and over the bound, for every mode
  slow      slow reader, non-reading peer deadline and shutdown remainder,
            for the modes with per-connection writers
  order     completion-order replies of the continuous mode accepted by this
            frontend and, with --portable-binary, by another load caller
  compare   the same load in every mode, with equal proof bytes required
  memory    a stalled reader against a small return budget, with the whole
            process memory growth bounded

The runner starts and stops only its own child processes, never retries, and
never changes sources or expected hashes. Each check writes its raw logs under
--out; report.json records PASS or the first failure.
"""
import argparse
import copy
import ctypes
import hashlib
import json
import math
import os
from pathlib import Path
import queue
import socket
import struct
import subprocess
import threading
import time

MAX_JSON = 2 * 1024 * 1024
MAX_PROOF = 16 * 1024 * 1024
MODES = ["original", "queued-return", "batch-fused", "continuous"]
WRITER_MODES = ["queued-return", "batch-fused", "continuous"]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    with path.open("x", encoding="utf-8") as f:
        json.dump(value, f, indent=2)
        f.write("\n")


def records(path):
    with path.open(encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def command(binary, role, options):
    result = [str(binary), role]
    for name, value in options.items():
        result += ["--" + name.replace("_", "-"), str(value)]
    return result


def clean_environment():
    # Settings must not silently come from the caller's SSGR_* variables.
    return {k: v for k, v in os.environ.items() if not k.startswith("SSGR_")}


class FrameEof(EOFError):
    def __init__(self, section, expected, received):
        self.section, self.expected, self.received = section, expected, received
        super().__init__(f"EOF in {section}: {received}/{expected} bytes")


def exact(sock, n, section="frame"):
    expected = n
    parts = []
    while n:
        piece = sock.recv(n)
        if not piece:
            raise FrameEof(section, expected, expected - n)
        parts.append(piece)
        n -= len(piece)
    return b"".join(parts)


def reply(sock):
    n, = struct.unpack("!I", exact(sock, 4, "header-length"))
    assert 0 < n <= MAX_JSON
    head = json.loads(exact(sock, n, "header-json"))
    p, = struct.unpack("!I", exact(sock, 4, "proof-length"))
    assert p <= MAX_PROOF and p == head["encoded_bytes"]
    return head, exact(sock, p, "proof-body")


def send_request(sock, job):
    data = json.dumps(job, separators=(",", ":")).encode()
    assert len(data) <= MAX_JSON
    sock.sendall(struct.pack("!I", len(data)) + data)


def job(input_value, job_id, run_id="network-controls"):
    return {"protocol": 1, "run_id": run_id, "job_id": job_id, "fixture_id": 0,
            "repeat": 1, "warmup": False, "scheduled_unix_ns": time.time_ns(),
            "deadline_unix_ns": time.time_ns() + 10_000_000_000, "input": input_value}


def process_sample(pid):
    """Whole-process current and peak RSS plus CPU; None when unavailable."""
    if os.name == "nt":
        from ctypes import wintypes

        class Counters(ctypes.Structure):
            _fields_ = [("cb", wintypes.DWORD), ("faults", wintypes.DWORD)] + [
                (n, ctypes.c_size_t) for n in ["peak", "rss", "paged_peak", "paged", "nonpaged_peak",
                                               "nonpaged", "pagefile", "pagefile_peak"]]
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        psapi = ctypes.WinDLL("psapi", use_last_error=True)
        kernel.OpenProcess.restype = wintypes.HANDLE
        kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel.CloseHandle.argtypes = [wintypes.HANDLE]
        psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
        kernel.GetProcessTimes.argtypes = [wintypes.HANDLE] + [ctypes.POINTER(ctypes.c_ulonglong)] * 4
        handle = kernel.OpenProcess(0x0400 | 0x0010, False, pid)
        if not handle:
            return None
        try:
            c = Counters()
            c.cb = ctypes.sizeof(c)
            times = [ctypes.c_ulonglong() for _ in range(4)]
            if not psapi.GetProcessMemoryInfo(handle, ctypes.byref(c), c.cb):
                return None
            have_cpu = kernel.GetProcessTimes(handle, *(ctypes.byref(t) for t in times))
            return {"rss_bytes": c.rss, "peak_rss_bytes": c.peak,
                    "cpu_seconds": (times[2].value + times[3].value) / 1e7 if have_cpu else None}
        finally:
            kernel.CloseHandle(handle)
    try:
        text = Path(f"/proc/{pid}/status").read_text()
        fields = {line.split(":", 1)[0]: line.split(":", 1)[1] for line in text.splitlines() if ":" in line}
        stat = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return {"rss_bytes": int(fields["VmRSS"].split()[0]) * 1024,
                "peak_rss_bytes": int(fields["VmHWM"].split()[0]) * 1024,
                "cpu_seconds": (int(stat[11]) + int(stat[12])) / os.sysconf("SC_CLK_TCK")}
    except (FileNotFoundError, KeyError, ValueError, PermissionError):
        return None


class Server:
    def __init__(self, binary, folder, mode, **overrides):
        self.folder = folder
        folder.mkdir()
        self.stderr = (folder / "stderr.txt").open("w", encoding="utf-8")
        self.stdout = (folder / "stdout.txt").open("w", encoding="utf-8")
        options = dict(out=folder / "Raw", listen="127.0.0.1:0", serving_mode=mode, workers=2, depth=3,
                       batch_max=8, max_wait_us=1000, max_queue=1024, run_ms=3000,
                       io_timeout_ms=5000, control_samples=1, telemetry_ms=20, log_flush_every=1,
                       return_jobs=8, return_bytes=MAX_PROOF, max_connections=16)
        if mode == "continuous":
            options["max_in_flight"] = 2
        options.update(overrides)
        self.options = options
        self.argv = command(binary, "server", options)
        self.proc = subprocess.Popen(self.argv, stdout=subprocess.PIPE, stderr=self.stderr,
                                     text=True, encoding="utf-8", env=clean_environment())
        self.samples = []
        self.ready_queue = queue.Queue()
        self.monitor_stop = threading.Event()
        self.reader = threading.Thread(target=self._stdout, daemon=True)
        self.monitor = threading.Thread(target=self._monitor, daemon=True)
        self.reader.start()
        self.monitor.start()
        try:
            self.ready = self.ready_queue.get(timeout=120)
            if self.ready is None:
                raise RuntimeError("server exited before READY")
            self.ready_sample = process_sample(self.proc.pid)
        except BaseException:
            self.close()
            raise
        host, port = self.ready["listen"].rsplit(":", 1)
        self.address = (host, int(port))

    def _stdout(self):
        for line in self.proc.stdout:
            self.stdout.write(line)
            self.stdout.flush()
            try:
                value = json.loads(line)
                if value.get("status") == "SERVER_READY":
                    self.ready_queue.put(value)
            except json.JSONDecodeError:
                pass
        self.ready_queue.put(None)

    def _monitor(self):
        while not self.monitor_stop.wait(0.02):
            observation = process_sample(self.proc.pid)
            if observation:
                self.samples.append({"observed_unix_ns": time.time_ns(), **observation})

    def controls(self):
        return {r["kind"]: r for r in records(self.folder / "Raw/server.jsonl") if r["event"] == "control"}

    def finish(self, timeout=60):
        exit_code = self.proc.wait(timeout=timeout)
        self.close()
        assert exit_code == 0, f"server exit {exit_code}: {self.folder}"
        terminal = json.loads((self.folder / "Raw/terminal.json").read_text())
        assert terminal["status"] == "SERVER_STOPPED", terminal
        b = terminal["return_budget"]
        assert b["resident_jobs"] == b["resident_bytes"] == 0
        assert b["peak_jobs"] <= b["max_jobs"] and b["peak_bytes"] <= b["max_bytes"]
        return terminal

    def close(self):
        killed = self.proc.poll() is None
        if killed:
            self.proc.kill()
            self.proc.wait(timeout=5)
        self.monitor_stop.set()
        self.reader.join(timeout=2)
        self.monitor.join(timeout=2)
        self.stdout.close()
        self.stderr.close()
        if not (self.folder / "process.json").exists():
            dump(self.folder / "process.json", {"pid": self.proc.pid, "argv": self.argv,
                 "exit_code": self.proc.returncode, "killed_by_runner": killed,
                 "sampling_period_ms": 20, "ready_sample": getattr(self, "ready_sample", None),
                 "samples": self.samples,
                 "peak_rss_bytes": max((s["peak_rss_bytes"] for s in self.samples), default=None)})


def load(binary, folder, target, expected=0, allow_receive_cutoff=False, older_caller=False, **overrides):
    folder.mkdir()
    options = dict(out=folder / "Raw", targets=f"{target[0]}:{target[1]}", depth=3,
                   verify_workers=2, corpus=2, control_samples=1, rate=50, jobs=12,
                   warmup_jobs=0, deadline_ms=3000, drain_ms=2000, telemetry_ms=20,
                   log_flush_every=1, run_id=folder.name)
    options.update(overrides)
    argv = command(binary, "load", options)
    with (folder / "stdout.txt").open("w") as stdout, (folder / "stderr.txt").open("w") as stderr:
        p = subprocess.run(argv, stdout=stdout, stderr=stderr, env=clean_environment(), timeout=300)
    assert (p.returncode == 0) == (expected == 0), (p.returncode, folder)
    terminal = json.loads((folder / "Raw/terminal.json").read_text(encoding="utf-8"))
    if expected == 0:
        assert terminal["status"] == "LOAD_OBSERVATIONS_COMPLETE"
        if allow_receive_cutoff:
            assert terminal["receive_drain_limit_reached"]
            assert terminal["pending_at_receive_drain_end"]
        else:
            # Older load callers do not report the receive cutoff separately;
            # their unresolved count below still covers every job.
            if "receive_drain_limit_reached" in terminal:
                assert not terminal["receive_drain_limit_reached"], "receive-drain cutoff reached"
            assert terminal["rejected_including_warmup"] == 0
            assert terminal["unresolved_at_drain"] == 0
            assert terminal["generator_failures"] == 0
            assert terminal["unexpected_response_count"] == 0
            if older_caller:
                # An older caller counts the server's orderly close after the
                # last reply as a receive error. Allow exactly that and only
                # after every reply was received.
                rows = records(folder / "Raw/frontend.jsonl")
                errors = [r for r in rows if r["event"] in ("receive_error", "send_error")]
                last = max(r["receive_end_unix_ns"] for r in rows if r["event"] == "received")
                assert len(errors) == terminal["transport_error_events"] <= 1
                assert all(r["event"] == "receive_error" and r["error"] == "peer closed frame"
                           and r["observed_unix_ns"] >= last for r in errors), errors
            else:
                assert terminal["transport_error_events"] == 0
            assert (terminal["accepted_by_deadline_including_warmup"]
                    + terminal["accepted_late_including_warmup"] == terminal["scheduled_jobs"])
    dump(folder / "process.json", {"argv": argv, "exit_code": p.returncode, "terminal": terminal})
    return terminal


class Proxy:
    def __init__(self, target, mutation):
        self.listener = socket.socket()
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(1)
        self.listener.settimeout(60)
        self.address = self.listener.getsockname()
        self.target, self.mutation = target, mutation
        self.changed, self.errors = [], []
        self.sockets = []
        self.thread = threading.Thread(target=self.run, daemon=True)
        self.thread.start()

    def run(self):
        try:
            front, _ = self.listener.accept()
            back = socket.create_connection(self.target, timeout=30)
            self.sockets = [front, back]
            front.settimeout(30)

            def forward():
                try:
                    while data := front.recv(65536):
                        back.sendall(data)
                    back.shutdown(socket.SHUT_WR)
                except OSError:
                    pass
            threading.Thread(target=forward, daemon=True).start()
            while True:
                head, proof = reply(back)
                if head["fixture_id"] == 1 and proof and not self.changed:
                    original_id = head["job_id"]
                    if self.mutation == "proof":
                        proof = proof[:-1] + bytes([proof[-1] ^ 1])
                        # Defeat the transport hash guard on purpose, so the
                        # encoded verifier itself must reject fixture 1, which
                        # has no cached control hash (control_samples=1).
                        head["canonical_sha256"] = sha(proof)
                    elif self.mutation == "job-id":
                        head["job_id"] += 1_000_000
                    elif self.mutation == "run-id":
                        head["run_id"] += "-wrong"
                    self.changed.append({"job_id": original_id, "fixture_id": 1, "mutation": self.mutation})
                data = json.dumps(head, separators=(",", ":")).encode()
                front.sendall(struct.pack("!I", len(data)) + data + struct.pack("!I", len(proof)) + proof)
        except (EOFError, OSError) as e:
            self.errors.append(type(e).__name__ + ": " + str(e))
        finally:
            for sock in self.sockets:
                sock.close()
            self.listener.close()

    def close(self):
        for sock in self.sockets:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
        self.thread.join(timeout=5)
        assert not self.thread.is_alive(), "proxy did not stop"


def invalid_cli(binary, out):
    cases = [["--serving-mode", "wrong"], ["--return-mode", "queued"], ["--return-jobs", "0"],
             ["--return-bytes", "0"], ["--max-connections", "0"], ["--workers", "0"],
             ["--max-in-flight", "0"], ["--workers", "2", "--max-in-flight", "3"],
             ["--depth", "4294967299"], ["--io-timeout-ms", "0"], ["--run-ms", "0"],
             ["--workers", "2", "--workers", "2"], ["--return-jobs"], ["--unknown", "1"],
             ["--return-bytes", "-1"], ["--host-id", "x" * 257]]
    result = []
    for i, args in enumerate(cases):
        destination = out / f"Invalid-{i}"
        run = subprocess.run([str(binary), "server", "--out", str(destination), *args],
                             capture_output=True, text=True, encoding="utf-8", env=clean_environment(), timeout=20)
        assert run.returncode != 0 and not destination.exists(), (args, run.stdout, run.stderr)
        result.append({"args": args, "exit_code": run.returncode, "stderr": run.stderr})
    return result


def smoke(args, out):
    result = {"invalid_cli": invalid_cli(args.binary, out)}
    for mode in args.modes:
        row = {}
        server = Server(args.binary, out / f"Normal-{mode}-server", mode)
        try:
            row["normal"] = load(args.binary, out / f"Normal-{mode}-load", server.address)
            inputs = server.controls()
            with socket.create_connection(server.address, timeout=10) as sock:
                for i, alter in enumerate(["field", "key", "kind"]):
                    value = copy.deepcopy(inputs["membership"]["input"])
                    if alter == "field":
                        value["old_root"][0] = 2_130_706_433
                    if alter == "key":
                        value["key"] = 1 << 24
                    if alter == "kind":
                        value["kind"] = "unknown"
                    send_request(sock, job(value, 10_000 + i))
                    head, proof = reply(sock)
                    assert head["job_id"] == 10_000 + i and head["run_id"] == "network-controls"
                    assert head["error"] and not proof
            row["normal_server"] = server.finish()
        finally:
            server.close()
        for mutation in ["proof", "job-id", "run-id"]:
            server = Server(args.binary, out / f"Mutation-{mode}-{mutation}-server", mode, run_ms=2500)
            proxy = Proxy(server.address, mutation)
            try:
                path = out / f"Mutation-{mode}-{mutation}-load"
                terminal = load(args.binary, path, proxy.address, expected=1,
                                jobs=2, mixture="membership:1", rate=20, corpus=2)
                assert terminal["status"] == "FAIL_SEMANTIC_GUARD"
                assert len(proxy.changed) == 1
                data = records(path / "Raw/frontend.jsonl")
                if mutation == "proof":
                    bad = [r for r in data if r["event"] == "completed" and r["fixture_id"] == 1]
                    assert len(bad) == 1 and not bad[0]["accepted"]
                    assert bad[0]["reply_binding"] and bad[0]["reply_hash_matches"]
                    assert bad[0]["control_reference_hash_matches"] is None
                if mutation == "job-id":
                    assert terminal["unexpected_response_count"] == 1
                if mutation == "run-id":
                    assert any(r["event"] == "completed" and not r["reply_binding"] for r in data)
                proxy.close()
                row[mutation] = {"changed": proxy.changed, "frontend": terminal, "server": server.finish()}
            finally:
                proxy.close()
                server.close()
        server = Server(args.binary, out / f"Receive-cutoff-{mode}-server", mode, run_ms=2500,
                        workers=1, max_in_flight=1) if mode == "continuous" else \
            Server(args.binary, out / f"Receive-cutoff-{mode}-server", mode, run_ms=2500, workers=1)
        try:
            row["receive_cutoff"] = load(args.binary, out / f"Receive-cutoff-{mode}-load", server.address,
                                         allow_receive_cutoff=True, jobs=256, rate=1_000_000, drain_ms=0)
            row["receive_cutoff_server"] = server.finish()
        finally:
            server.close()
        result[mode] = row
    return result


def burst(server, jobs, pause_seconds, read_results):
    control = server.controls()["membership"]
    sock = socket.socket()
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 4096)
    sock.settimeout(60)
    sock.connect(server.address)
    sent, received, errors, frames = [], [], [], []
    detail = {"scheduled_jobs": jobs, "read_results": read_results, "pause_seconds": pause_seconds,
              "start_unix_ns": time.time_ns(),
              "initial_receive_buffer_bytes": sock.getsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF)}

    def send():
        try:
            for i in range(jobs):
                send_request(sock, job(control["input"], i))
                sent.append(i)
            sock.shutdown(socket.SHUT_WR)
        except OSError as e:
            errors.append(str(e))
    sender = threading.Thread(target=send, daemon=True)
    sender.start()
    try:
        time.sleep(pause_seconds)
        if read_results:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
            while True:
                try:
                    head, proof = reply(sock)
                    frames.append({"job_id": head["job_id"], "run_id": head["run_id"], "encoded_bytes": len(proof),
                                   "proof_sha256": sha(proof), "error": head["error"], "received_unix_ns": time.time_ns()})
                    assert head["run_id"] == "network-controls"
                    if not head["error"]:
                        assert sha(proof) == head["canonical_sha256"] == control["canonical_sha256"]
                    else:
                        assert not proof
                    received.append(head["job_id"])
                except FrameEof as e:
                    detail["read_end"] = {"type": type(e).__name__, "section": e.section,
                                          "expected_bytes": e.expected, "received_bytes": e.received}
                    if e.section != "header-length" or e.received != 0:
                        raise
                    break
                except ConnectionResetError as e:
                    detail["read_end"] = {"type": type(e).__name__, "message": str(e)}
                    break
        terminal = server.finish(timeout=90)
        events = records(server.folder / "Raw/server.jsonl")
        arrivals = [e["job_id"] for e in events if e["event"] == "server_arrival"]
        returns = [e["reply"]["job_id"] for e in events if e["event"] in ("server_return", "server_reject")]
        detail.update({"terminal": terminal, "arrival_ids": arrivals, "return_attempt_ids": returns,
                       "missing_return_attempt_ids": sorted(set(arrivals) - set(returns)),
                       "missing_received_ids": sorted(set(arrivals) - set(received)),
                       "unexpected_received_ids": sorted(set(received) - set(arrivals))})
        writes = [{"job_id": e["reply"]["job_id"], "write_duration_ns": e.get("write_duration_ns"),
                   "wire_bytes": e.get("wire_bytes"), "error": e.get("write_error"),
                   "error_kind": e.get("write_error_kind"), "raw_os_error": e.get("write_error_raw_os_error"),
                   "progress": e.get("write_progress")} for e in events if e["event"] in ("server_return", "server_reject")]
        detail["writes"] = writes
        assert len(returns) == len(set(returns)), "duplicate return attempt IDs"
        assert set(arrivals) == set(returns), "received jobs without exactly one return attempt"
        if read_results:
            assert terminal["response_write_failures"] == 0, f"server write failures: {terminal['response_write_failures']}"
            assert set(received) == set(arrivals) and len(received) == len(set(received)), "receive/admission ID mismatch"
        return {"terminal": terminal, "sent_count": len(sent), "received_count": len(received),
                "arrival_count": len(arrivals), "sender_errors": errors, "writes": writes,
                "max_write_ns": max((e.get("write_duration_ns", 0) for e in events), default=0)}
    finally:
        sock.close()
        sender.join(timeout=5)
        detail.update({"finish_unix_ns": time.time_ns(), "sent_ids": sent, "received_ids": received,
                       "frames": frames, "sender_errors": errors, "sender_finished": not sender.is_alive()})
        dump(server.folder / "burst-observations.json", detail)
        assert not sender.is_alive(), "sender did not stop"


def metadata(args, out):
    result = {}
    for mode in args.modes:
        server = Server(args.binary, out / f"Metadata-{mode}-server", mode, run_ms=2500)
        observed = []
        try:
            control = server.controls()["membership"]
            cases = [("run-id-at-limit", "x" * 256, "membership", False),
                     ("kind-at-limit", "valid", "x" * 64, False),
                     ("run-id-over-limit", "x" * 257, "membership", True),
                     ("kind-over-limit", "valid", "x" * 65, True)]
            for index, (name, run_id, kind, closes) in enumerate(cases):
                value = copy.deepcopy(control["input"])
                value["kind"] = kind
                with socket.create_connection(server.address, timeout=10) as sock:
                    request = job(value, 1000 + index, run_id)
                    send_request(sock, request)
                    try:
                        head, proof = reply(sock)
                        assert not closes, name
                        assert head["job_id"] == request["job_id"] and head["run_id"] == run_id
                        if kind == "membership":
                            assert head["error"] is None and sha(proof) == control["canonical_sha256"]
                        else:
                            assert head["error"] and not proof
                        observed.append({"case": name, "outcome": "response", "error": head["error"]})
                    except FrameEof as e:
                        assert closes and e.section == "header-length" and e.received == 0, name
                        observed.append({"case": name, "outcome": "closed_before_admission"})
            terminal = server.finish()
            assert terminal["responses_written"] == 2 and terminal["response_write_failures"] == 0
            result[mode] = {"cases": observed, "terminal": terminal}
        finally:
            server.close()
    return result


def slow(args, out):
    result = {}
    for mode in [m for m in args.modes if m in WRITER_MODES]:
        row = {}
        server = Server(args.binary, out / f"Slow-{mode}-server", mode, run_ms=10_000, return_jobs=1, io_timeout_ms=5000)
        try:
            good = burst(server, args.burst_jobs, 2.0, True)
            assert good["max_write_ns"] > 100_000_000, "real socket backpressure was not reached"
            assert good["terminal"]["return_budget"]["wait_ns"] > 100_000_000, "real return-budget wait was not reached"
            assert all(w["progress"]["bytes_written"] == w["wire_bytes"] for w in good["writes"]), "frame byte accounting differs"
            assert all(not w["progress"]["deadline_expired"] for w in good["writes"])
            row["slow_reader"] = good
        finally:
            server.close()
        server = Server(args.binary, out / f"Nonreading-{mode}-server", mode, run_ms=1500, return_jobs=1, io_timeout_ms=200)
        try:
            timeout = burst(server, args.burst_jobs, 2.0, False)
            failures = [w for w in timeout["writes"] if w["error"] is not None]
            assert failures, "socket write deadline was not exercised"
            first = failures[0]
            assert first["error_kind"] == "TimedOut", f"first failure was not a frame timeout: {first}"
            assert first["progress"]["deadline_expired"], "deadline consumer did not fire"
            assert first["progress"]["would_block"] + first["progress"]["timed_out"] > 0, "no real kernel backpressure observed"
            # No early tolerance: an immediate WouldBlock or NotConnected cannot
            # pass. The upper 250 ms is scheduling slack for this local fixture.
            assert 200_000_000 <= first["write_duration_ns"] <= 450_000_000, f"timeout outside 200..450 ms: {first}"
            timeout["first_deadline_frame"] = first
            timeout["later_error_kinds"] = sorted({str(w["error_kind"]) for w in failures[1:]})
            row["nonreading_peer"] = timeout
        finally:
            server.close()
        extra = {"max_in_flight": 1} if mode == "continuous" else {}
        server = Server(args.binary, out / f"Shutdown-{mode}-server", mode, run_ms=400, return_jobs=1,
                        workers=1, batch_max=1, **extra)
        try:
            shutdown = burst(server, args.burst_jobs, 0, True)
            assert shutdown["terminal"]["unprocessed_jobs"] > 0, "shutdown remainder branch was not reached"
            row["shutdown_remainder"] = shutdown
        finally:
            server.close()
        result[mode] = row
    return result


def inversions(sequence):
    return sum(1 for i in range(len(sequence)) for j in range(i + 1, len(sequence)) if sequence[i] > sequence[j])


def order(args, out):
    """Completion-order replies must be accepted by every load caller used."""
    callers = [("serving-frontend", args.binary, False)]
    if args.portable_binary:
        callers.append(("portable-caller", args.portable_binary, True))
    result = {}
    for name, caller, older in callers:
        server = Server(args.binary, out / f"Order-{name}-server", "continuous", depth=args.order_depth,
                        workers=4, max_in_flight=4, run_ms=int(args.order_jobs / args.order_rate * 1000) + 20_000,
                        log_flush_every=256)
        try:
            terminal = load(caller, out / f"Order-{name}-load", server.address, older_caller=older,
                            depth=args.order_depth,
                            rate=args.order_rate, jobs=args.order_jobs, corpus=8, verify_workers=4,
                            deadline_ms=60_000, drain_ms=30_000, log_flush_every=256)
            server_terminal = server.finish(timeout=120)
            events = records(server.folder / "Raw/server.jsonl")
            arrivals = [e["job_id"] for e in events if e["event"] == "server_arrival"]
            returns = [e["reply"]["job_id"] for e in events if e["event"] == "server_return"]
            moved = inversions(returns)
            assert sorted(returns) == sorted(arrivals) == list(range(args.order_jobs)), "reply set differs from requests"
            assert moved > 0, "ORDER_NOT_EXERCISED: replies left in arrival order, so reordering was not tested"
            frontend = records(out / f"Order-{name}-load/Raw/frontend.jsonl")
            accepted = [r for r in frontend if r["event"] == "completed" and r["accepted"]]
            assert len(accepted) == args.order_jobs
            result[name] = {"frontend": terminal, "server": server_terminal, "reply_order_inversions": moved,
                            "arrival_order_equals_reply_order": arrivals == returns}
        finally:
            server.close()
    return result


def percentile(values, p):
    values = sorted(values)
    return values[max(0, math.ceil(len(values) * p) - 1)] if values else None


def measurement(path):
    frontend = records(path / "Load/Raw/frontend.jsonl")
    timed = [r for r in frontend if r["event"] == "completed" and not r["warmup"]]
    offered = [r for r in frontend if r["event"] == "offered" and not r["warmup"]]
    assert len(timed) == len(offered) and all(r["accepted"] for r in timed)
    latency = [r["scheduled_to_accept_ns"] / 1e6 for r in timed]
    start = min(r["scheduled_unix_ns"] for r in offered)
    end = max(r["accepted_end_unix_ns"] for r in timed)
    server = records(path / "Server/Raw/server.jsonl")
    returns = [r for r in server if r["event"] == "server_return"]
    batches = [r for r in server if r["event"] == "server_batch"]
    stages = [r["job_stages"] for r in returns if r.get("job_stages")]
    typed_drop = [r["typed_drop_ns"] for r in batches if r.get("typed_drop_ns") is not None]
    batch_jobs = sum(r["jobs"] for r in batches if r.get("typed_drop_ns") is not None)
    return {"timed_jobs": len(timed), "p50_ms": percentile(latency, .5), "p99_ms": percentile(latency, .99),
            "max_ms": max(latency), "completion_span_seconds": (end - start) / 1e9,
            "accepted_per_completion_second": len(timed) * 1e9 / (end - start),
            "server_write_ns_including_warmup": sum(r["write_duration_ns"] for r in returns),
            "return_path_hash_ns_including_warmup": sum(r.get("hash_ns", 0) for r in returns),
            "dispatcher_typed_release_ns_per_job": (sum(typed_drop) / batch_jobs) if batch_jobs else None,
            "worker_release_ns_per_job": (sum(s["release_ns"] for s in stages) / len(stages)) if stages else None,
            "worker_release_on_worker_fraction": (sum(s["release_tid"] == s["worker_tid"] for s in stages) / len(stages)) if stages else None,
            "server_process": json.loads((path / "Server/process.json").read_text()),
            "proofs": sorted({(r["kind"], r["fixture_id"], r["canonical_sha256"]) for r in timed})}


def compare(args, out):
    results = []
    # Reverse each repeat's order to reduce systematic warm-cache and order bias.
    for repeat in range(args.repeats):
        modes = list(args.modes)
        if repeat % 2:
            modes.reverse()
        for mode in modes:
            path = out / f"Compare-{repeat + 1}-{mode}"
            path.mkdir()
            server = Server(args.binary, path / "Server", mode, depth=args.depth, workers=args.workers,
                            batch_max=args.batch, max_wait_us=args.wait_us,
                            run_ms=int(args.seconds * 1000 + 15000), log_flush_every=256,
                            **({"max_in_flight": args.workers} if mode == "continuous" else {}))
            try:
                load(args.binary, path / "Load", server.address, depth=args.depth, rate=args.rate,
                     duration_sec=args.seconds, warmup_jobs=6, deadline_ms=30_000, drain_ms=10_000,
                     log_flush_every=256, corpus=min(4, (1 << min(args.depth, 24)) - 1))
                server.finish(timeout=args.seconds + 40)
            finally:
                server.close()
            results.append({"repeat": repeat + 1, "mode": mode, **measurement(path)})
    reference = results[0]["proofs"]
    assert all(r["proofs"] == reference for r in results), "proof bytes differ across serving modes"
    return {"configuration": {k: getattr(args, k) for k in ["depth", "workers", "batch", "wait_us", "rate", "seconds", "repeats"]},
            "measurements": results,
            "interpretation": "Finite local paired observations of one machine. They establish equal proof bytes across modes and show where release happens; they are not capacity or speedup evidence."}


def memory(args, out):
    """A stalled reader must stop computation at the return budget."""
    mode = "continuous"
    in_flight, return_jobs = 4, 4
    # Rows are flushed one by one so the burst can read the startup controls.
    server = Server(args.binary, out / "Memory-server", mode, depth=args.memory_depth, workers=in_flight,
                    max_in_flight=in_flight, return_jobs=return_jobs, run_ms=30_000, io_timeout_ms=60_000)
    try:
        baseline = server.ready_sample
        assert baseline, "process memory sampling is unavailable on this platform"
        observed = burst(server, args.memory_jobs, args.memory_pause, True)
        stalled = [s for s in server.samples if s["observed_unix_ns"] < observed["terminal"]["finish_unix_ns"]]
        peak = max(s["peak_rss_bytes"] for s in server.samples)
        growth = peak - baseline["rss_bytes"]
        # Encoded proofs are about 0.18 MiB at depth 24; one job's typed peak is
        # below 1 MiB. The bound allows four times that per resident job plus
        # 64 MiB for stacks, socket buffers, the queue of small requests and
        # allocator retention. An unbounded return queue at this burst size
        # would hold memory_jobs encoded proofs instead.
        per_job = 4 * 1024 * 1024
        bound = (in_flight + return_jobs) * per_job + 64 * 1024 * 1024
        unbounded = args.memory_jobs * 180 * 1024
        assert unbounded > bound, "fixture too small to separate a bounded from an unbounded return path"
        budget = observed["terminal"]["return_budget"]
        assert budget["peak_jobs"] == return_jobs, "return budget was never saturated"
        assert budget["wait_ns"] > 0, "producers never waited on the return budget"
        assert growth <= bound, f"memory growth {growth} exceeds bound {bound}"
        return {"baseline_rss_bytes": baseline["rss_bytes"], "peak_rss_bytes": peak, "growth_bytes": growth,
                "bound_bytes": bound, "unbounded_estimate_bytes": unbounded, "return_budget": budget,
                "samples_during_run": len(stalled), "burst": {k: observed[k] for k in ["sent_count", "received_count", "arrival_count"]}}
    finally:
        server.close()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--portable-binary", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--suite", choices=["smoke", "metadata", "slow", "order", "compare", "memory", "all"], default="smoke")
    p.add_argument("--modes", default=",".join(MODES))
    p.add_argument("--burst-jobs", type=int, default=256)
    p.add_argument("--depth", type=int, default=3)
    p.add_argument("--workers", type=int, default=2)
    p.add_argument("--batch", type=int, default=8)
    p.add_argument("--wait-us", type=int, default=1000)
    p.add_argument("--rate", type=float, default=50)
    p.add_argument("--seconds", type=float, default=3)
    p.add_argument("--repeats", type=int, default=3)
    p.add_argument("--order-depth", type=int, default=12)
    p.add_argument("--order-jobs", type=int, default=96)
    p.add_argument("--order-rate", type=float, default=200)
    p.add_argument("--memory-depth", type=int, default=24)
    p.add_argument("--memory-jobs", type=int, default=768)
    p.add_argument("--memory-pause", type=float, default=6.0)
    args = p.parse_args()
    args.binary = args.binary.resolve(strict=True)
    if args.portable_binary:
        args.portable_binary = args.portable_binary.resolve(strict=True)
    args.modes = args.modes.split(",")
    assert args.modes and all(m in MODES for m in args.modes), args.modes
    assert 1 <= args.depth <= 32 and min(args.workers, args.batch, args.burst_jobs, args.repeats) > 0
    assert math.isfinite(args.rate) and args.rate > 0 and math.isfinite(args.seconds) and args.seconds > 0
    args.out = args.out.resolve()
    args.out.mkdir(parents=True, exist_ok=False)
    report = {"status": "RUNNING", "suite": args.suite, "modes": args.modes, "start_unix_ns": time.time_ns(),
              "binary_sha256": sha(args.binary.read_bytes()),
              "portable_sha256": sha(args.portable_binary.read_bytes()) if args.portable_binary else None,
              "host": {"platform": os.name, "cpu_count": os.cpu_count()}, "results": {}}
    try:
        for name, function in [("smoke", smoke), ("metadata", metadata), ("slow", slow), ("order", order),
                               ("compare", compare), ("memory", memory)]:
            if args.suite in (name, "all"):
                report["results"][name] = function(args, args.out)
        report["status"] = "PASS"
    except BaseException as e:
        report["status"] = "FAIL"
        report["error"] = f"{type(e).__name__}: {e}"
        raise
    finally:
        report["finish_unix_ns"] = time.time_ns()
        dump(args.out / "report.json", report)
        print(json.dumps({"status": report["status"], "report": str(args.out / "report.json")}))


if __name__ == "__main__":
    main()
