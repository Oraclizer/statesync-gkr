# Serving components and reference proof server

The prover library produces and verifies proofs. A proof service also has to
bind replies to requests, refuse work it cannot hold, bound frames and memory,
write replies to slow peers without stalling everyone else, and keep the
cores busy between requests. This crate packages those parts as a library,
composes them into a reference server with four serving modes, and ships a
load frontend and real-TCP checks.

The crate is a standalone Cargo workspace. It depends on the product only
through the public `statesync-gkr` API, and its lock file uses the product
lock's dependency versions. Nothing here changes the product workspace,
proof format, verifier acceptance conditions or transcript order.

## Components (`ssgkr_serving`)

| Module | What it gives an integrating service |
|---|---|
| `wire` | The request and reply envelope bound to a run and job identifier, length-prefixed framing with frame and metadata limits checked before work is admitted, and a reply writer that holds one absolute deadline for a whole frame. |
| `admission` | A cap on admitted jobs that have not started computing, shared by every connection, and the explicit rejection reasons a client receives instead of unbounded queueing. |
| `budget` | A return budget in responses and encoded bytes. A permit stays charged through the frame write and its log row, so a stalled peer becomes backpressure on producers rather than memory growth. |
| `completion` | `complete`, which generates the witness, proves, encodes, hashes and releases the typed intermediates of one request on one thread; `complete_batch`, the same per job inside a Rayon pool; and `ContinuousRunner`, a fixed set of workers that each start the oldest waiting job as soon as they finish the previous one. |
| `timing` | Clocks, thread labels and `StageTimes`, the per-job record of dispatch, witness, proof, encoding, hash and release, including which thread released the job's memory. |
| `fixture` | The deterministic request constructor of the measured benchmark corpus. |

Proof bytes do not depend on the serving mode, thread or order. `complete`
calls `make_job_prepared` and `prove_batch_prepared` with a single job, the
same per-job proving path as the prover's sequential and parallel batch APIs,
and every proof transcript starts from its own job's public inputs. The
server re-checks this at startup: each control sample's fused completion must
produce the same bytes as the batch API before the server listens.

A minimal continuous service loop, as an excerpt (connection handling,
logging and error replies omitted):

```rust
use ssgkr_serving::completion::{complete, ContinuousRunner};
use std::sync::{mpsc, Arc};

let (ingress, queue) = mpsc::sync_channel(8192);
let shared = Arc::new((prover, prepared));
let runner = ContinuousRunner::spawn(workers, queue, move |request| {
    let (prover, prepared) = &*shared;
    match complete(prover, prepared, request) {
        Ok(done) => { /* acquire a return permit, then hand done.bytes to the writer */ }
        Err(e) => { /* reply with an explicit error */ }
    }
})?;
// Readers call admission.try_admit() and ingress.try_send(request); dropping
// every sender lets the workers drain the queue and stop.
```

## Serving modes of the reference server

| `--serving-mode` | Scheduling | Hash and release of typed data | Reply order |
|---|---|---|---|
| `original` | One FIFO per operation kind, the oldest ready kind first, flush at `--batch-max` or `--max-wait-us`; one compute batch at a time with parallel witness, proof and encoding phases | On the dispatcher, which hashes, writes and logs each result inline and then releases the typed batch | Batch order |
| `queued-return` | As `original` | The dispatcher releases the typed batch; per-connection writers hash and write while the next batch computes | Batch order |
| `batch-fused` | As `original` | Each job's witness, proof, encoding, hash and release run as one task on its worker inside the parallel stage; writers only write | Batch order |
| `continuous` (default) | One arrival-order FIFO across kinds; up to `--max-in-flight` workers each start the oldest admitted job when they finish the previous one | On the worker that computed the job | Completion order, matched by job identifier |

`original` reproduces the serving loop used for the earlier capacity
measurements, for comparisons inside one binary. Every mode shares the same
admission, rejection, framing, return budget and shutdown behavior.

## Run

```sh
cargo build --release --locked --manifest-path benches/serving/Cargo.toml
target=benches/serving/target/release/ssgkr-serving
"$target" server --out results/server-1 --listen 127.0.0.1:9400 --serving-mode continuous --workers 16 --max-in-flight 14
"$target" load --out results/load-1 --targets 127.0.0.1:9400 --rate 100 --duration-sec 30 --verify-workers 8
```

Build with `RUSTFLAGS="-C target-cpu=native"` for measurement; the default
build does not use the CPU vector extensions the field arithmetic benefits
from. Every result directory must be new; the server and frontend refuse to
overwrite files.

### Server options

| Option | Default | Meaning |
|---|---|---|
| `--serving-mode` | `continuous` | One of the four modes above |
| `--workers` | 48 | Compute pool threads; in `continuous`, the thread budget that bounds `--max-in-flight` |
| `--max-in-flight` | workers minus 2, at least 1 | `continuous` only: jobs computing at once, at most `--workers` |
| `--batch-max`, `--max-wait-us` | 96, 1000 | Batch modes: batch size cap and the oldest job's wait before a flush |
| `--max-queue` | 8192 | Admitted jobs not yet computing, across connections; beyond it requests are rejected |
| `--max-connections` | 64 | Concurrent connections; extra connections are closed |
| `--return-jobs`, `--return-bytes` | 192, 64 MiB | Return budget: resident finished responses and their encoded capacity |
| `--io-timeout-ms` | 5000 | Deadline for one whole reply frame; a missed deadline closes that connection |
| `--run-ms` | 600000 | Admission closes at this run limit |
| `--depth` | 24 | Sparse Merkle tree depth of the prepared circuits |
| `--control-samples` | 2 | Startup controls per kind |
| `--telemetry-ms` | 100 | Process telemetry period from `/proc` (0 disables) |
| `--log-flush-every` | 256 | Log rows per buffer flush |
| `--listen`, `--out`, `--host-id`, `--run-id`, `--repeat` | | Address and provenance |

Rejections carry one of `server_total_queue_full`, `server_ingress_queue_full`,
`server_stopping`, `server_run_limit_before_compute`,
`encoded_response_exceeds_return_budget`, or an `input:`, `witness:` or
`encode:` reason in the reply's `error` field, with an empty proof. At the run
limit, admitted jobs that have not started receive
`server_run_limit_before_compute`; jobs already computing finish and are sent.

The return budget counts encoded buffer capacity only. Jobs in progress (one
batch, or up to `--max-in-flight` jobs), prepared circuits, request frames,
thread stacks, socket buffers and allocator overhead are outside it, so
compare whole-process memory separately.

## Records

The server writes `metadata.json`, `server.jsonl` and `terminal.json`; the
frontend writes `metadata.json`, `frontend.jsonl`, `fixtures.jsonl` and
`terminal.json`. Server rows keep the fields of the earlier capacity caller
and add `mode`, `connection` and `writer_tid` on reply rows, with
`job_stages` in the fused modes:

| `job_stages` field | Meaning |
|---|---|
| `worker_tid`, `worker_os_tid` | Process thread label and, on Linux, the OS thread id of the computing worker |
| `dispatch_unix_ns` | Job start |
| `witness_ns`, `prove_ns`, `encode_ns`, `hash_ns`, `release_ns` | Stage durations on the worker |
| `release_tid` | Thread that freed the typed witness and proof |
| `return_enqueue_ns` | From job completion to the start of its frame write |
| `write_start_unix_ns`, `write_end_unix_ns` | Frame write interval |

In `batch-fused`, a batch row's witness and proof boundaries are those of the
latest job, and its encode end is the end of the parallel stage, which also
covers each job's hash and release. In `continuous` there are no batch rows;
a reply's batch fields describe its own job. Reply headers have the same
fields in every mode, so other load callers that speak this frame format
accept them unchanged.

## Checks

```sh
cargo fmt --manifest-path benches/serving/Cargo.toml --check
cargo clippy --manifest-path benches/serving/Cargo.toml --all-targets --locked -- -D warnings
cargo test --manifest-path benches/serving/Cargo.toml --release --locked
python3 benches/serving/service-checks.py --binary benches/serving/target/release/ssgkr-serving --suite smoke --out results/checks-1
```

`service-checks.py` runs real TCP suites against the built server:

| Suite | What must hold |
|---|---|
| `smoke` | Invalid options fail before any output; in every mode, a normal load is fully accepted, malformed inputs get explicit errors, a flipped proof byte, a changed job identifier and a changed run identifier are each caught by the frontend, and a zero receive drain reports its cutoff |
| `metadata` | Run and kind identifiers at the limit are served; one byte over closes the connection before admission |
| `slow` | Writer modes: a slow reader causes real socket backpressure and return-budget waits but no failed frame; a non-reading peer fails at one frame deadline; a run limit during a burst rejects the jobs that had not started |
| `order` | `continuous` replies leave out of arrival order and every reply is still accepted, by this frontend and, with `--portable-binary`, by another caller of the same frame format |
| `compare` | The same load in every mode gives the same proof bytes; per-mode latency and release location are recorded |
| `memory` | With a reader that stops reading, computation stops at the return budget and whole-process memory growth stays under an explicit bound |

These are functional checks on one machine. Their latencies are not capacity,
throughput or speedup evidence; controlled measurements are reported with the
benchmark results.

## License

Business Source License 1.1, the same terms as the product; see `LICENSE`.
