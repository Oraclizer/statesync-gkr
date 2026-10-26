# Performance and measured operating profiles

The evaluation asks three different questions: how much memory one layer's
prover owns, how quickly an internal computation completes, and which actual
arrival load reaches cryptographic acceptance within a stated latency budget.
These intervals have separate data and units. The [architecture guide](architecture.md)
connects the results to nine implementation benefits; [usage](usage.md)
describes their application conditions. The v1.2.0 sections come first and
pair each result with v1.1.0 measured on the same day; the sections after them
keep the earlier v1.1.0 campaigns as their own series.
The [replay guide](../benches/controlled-capacity-2026-10-07/README.md) contains
actual small-control commands. The [dataset locator](../benches/controlled-capacity-2026-10-07/DATASET_LOCATOR.json)
defines the complete raw/table/figure layout and its current preparation status.
The engineering paper, *StateSync-GKR: Design and Evaluation of a Reusable
Sparse GKR Engine*, is available as
[arXiv:2610.14849](https://arxiv.org/abs/2610.14849). It presents the engine
design and these controlled measurements. The separate dataset remains
prepared for review: the locator's publication URL, dataset DOI and archive
digest remain null. The engineering paper, existing software DOI and
[formal paper](https://arxiv.org/abs/2610.05335) identify different records;
none assigns a publication identifier to the new dataset.

The documentation's
[Benchmark results](https://oraclizer.io/ss-gkr/docs/benchmarks/results/) page
lists each result with its comparison target and conditions.

The v1.2.0 studies measured the release tag v1.2.0, commit
`8b2908160f36adc233d7b869a403d2ee4d3502a5`, and ran v1.1.0 on the same day, on
the same instance types and with the same corpus, frontend program and latency
budgets as the reference. Those hosts ran Amazon Linux 2023 with kernel 6.18,
while the earlier campaigns ran kernel 6.8; pairing the releases on the same
day keeps that difference out of the version comparisons. Ratios between
releases come from these same-day pairs unless a value names the earlier
campaign.

The earlier studies use the immutable v1.1.0 kernel. Its two C8a baremetal
campaigns contain 243 and 175 distinct process executions on different hosts.
The later v1.1.0 controlled study uses actual C8a 48/96/192-core VMs, fixed corpora,
separate frontend verification, generic same-driver memory contrasts and
bounded memory-limit tests. Changing a worker count on a large VM is separately
labelled and is not a measurement of a smaller machine.

## What v1.2.0 changes

Version 1.2.0 keeps the verifier, the proof format, the transcript order and
every proof byte. It changes how the sparse prover computes its round
messages, adds serving components with a reference proof server in
[`benches/serving`](../benches/serving/README.md), and refuses two misuses in
every build profile.

| Measure | v1.1.0 | v1.2.0 | Conditions |
| --- | --- | --- | --- |
| Highest offered rate with every timed request accepted within 1 s, one 192-core VM | 1,000/s in the earlier campaign; 1,150/s on the same day in one 60-s run, the highest rate tried | 3,300/s on one connection; at least 5,000/s on two | v1.2.0 continuous mode; 3,300/s confirmed in three 60-s runs; the two-connection value comes from 15-s screens at a frontend-limited point and is a lower bound |
| p99 at 1,000 requests/s, one 192-core VM | 433.8–475.1 ms | 33.7–33.9 ms | Three 60-s runs each, 16-core frontend |
| Highest offered rate within 1 s, one 96-core VM | 500/s; 1,000/s failed | 3,000/s; 4,000/s failed | Screens, not confirmations: one 15-s run per rate for v1.2.0 on the 48-core frontend, one 20-s run per rate for v1.1.0 |
| Highest offered rate within 1 s, one 48-core VM | 500/s; 1,000/s failed | 2,000/s; 2,400/s failed | Screens, not confirmations: one 15-s run per rate for each release |
| Compute cost per million requests at that rate, 192-core VM | USD 2.87 at 1,000/s; at most USD 2.50 at 1,150/s | USD 0.87 at 3,300/s | On-demand VM price, continuous operation, frontend excluded; the same-day v1.1.0 value is an upper bound because higher rates were not tried |
| Proving-only rate at 192 workers, bare metal | 3,195.50 / 2,947.08 / 2,102.02 per s | 7,713.71 / 7,220.36 / 5,390.07 per s | Membership / non-membership / update, depth 24, batch 768 |
| Prepared request p50 on one thread | 42.10 / 46.10 / 65.03 ms | 16.95 / 18.22 / 24.62 ms | Same operations at depth 24, three processes of 1,000 timed requests each |
| Allocation calls per proof | 1,282 | 85 | Mixed two-layer circuit of width 4,096, counting-allocator build |
| Release-build misuse checks | Debug builds only | Every build: `SyncError::KindMismatch`, and a wrong-width leaf pre-image panics | `src/lib.rs`, `crates/primitives/src/hash.rs` |

## Serving capacity on one server

The reference proof server ran in continuous mode on C8a VMs with 48, 96 and
192 cores. A separate frontend offered the membership/non-membership/update
1:1:1 mix at depth 24 from 192 fixed fixtures per kind, verified every complete
proof against its original request and timed each request from its scheduled
arrival to that acceptance. Both releases faced the same frontend program, the
load caller of the earlier v1.1.0 campaign. A rate passes when every repeat
accepted every timed request within one second. A point is marked
frontend-limited when the frontend used more than 70% of its cores or its
verification-wait p99 exceeded 50 ms while the server stayed below 90% CPU.
Such a point bounds the frontend, so it is left out when a server's highest
rate is judged. [Serving components](../benches/serving/README.md#settings-used-in-the-controlled-measurements)
lists the server settings.

### 192 cores and the network path

| Measure | v1.1.0, same day | v1.2.0 continuous | v1.2.0 batch-fused |
| --- | ---: | ---: | ---: |
| p99 at 1,000 requests/s, three 60-s runs | 433.8–475.1 ms | 33.7–33.9 ms | 95.6–96.0 ms |
| p99 at 1,150 requests/s, 60-s runs | 580.1 ms (one run) | 33.6 ms (three runs) | 96.1–96.3 ms (three runs) |
| Highest rate within 1 s on one connection, three 60-s runs | not measured above 1,150/s | 3,300/s, p99 35.4–38.5 ms | 3,300/s, p99 225.1–300.3 ms |

Every run in the first two rows accepted every timed request within one
second. The v1.1.0 record of the earlier campaign met one second at 1,000/s,
and at 1,150/s it accepted 70.37% within one second. The 3,300/s
confirmations used a 48-core frontend, because the 16-core frontend reached its
own limit at 2,000/s.

A 30-minute continuous run at 3,300 requests/s accepted all 5,940,000 timed
requests within one second, with p50 26.7 ms, p99 35.3 ms and maximum 58.8 ms.
Straight-line fits over the run give -0.006 pending requests and -0.006 ms of
cohort p99 per minute, and +0.08 MiB of server RSS per minute. A second
192-core VM reproduced the result: three 60-second runs at 3,300 requests/s
accepted every timed request within one second with p99 37.6–46.4 ms, and its
1,000/s p99 was 34.1 ms against 666.8 ms for v1.1.0 on that VM. These periods
describe the observations.

Each reply carries one complete encoded proof, on average about 182.6 kB on
the wire for this mix. At 3,300 requests/s one connection carried 4.82 Gbit/s
of reply frames. At 3,400 requests/s the reply traffic on one connection
levelled at about 4.96 Gbit/s while, in the one-connection runs up to that
rate, the server used at most 50% and the frontend at most 52% of their cores,
and the one-second budget failed in all three 60-second runs. This matches the cloud provider's documented 5-Gbit/s
limit for a single flow between instances outside a cluster placement group.
With two connections to the same server, 15-second screens met one second at
every rate from 3,400 to 5,000 requests/s, and the server sent 7.30 Gbit/s at
5,000/s. There the frontend used 74% of its cores and was marked
frontend-limited, so 5,000/s is a lower bound for the server. Reply traffic is
computed from the reply wire bytes of completed requests, before TCP/IP
headers. Above the one-connection limit the two modes degraded differently: at
3,500 and 4,000 requests/s continuous completions fell to about 2,000 to 2,200
per second, while batch-fused held about 3,270 to 3,290 per second.

### 48 and 96 cores

| Server | v1.1.0, same day | v1.2.0 continuous | What limited v1.2.0 |
| --- | --- | --- | --- |
| 48 cores | 500/s; 1,000/s failed with 7.9% within 1 s | 2,000/s with p99 147.0 ms; 2,400/s failed with 30.0% within 1 s | Server CPU at 96% |
| 96 cores | 500/s; 1,000/s failed with 21.1% within 1 s | 3,000/s with p99 37.6 ms; 4,000/s failed with 35.2% within 1 s | Reply transfer on one connection: server CPU at 83%, return budget full, replies at 4.95 Gbit/s |

These rates come from screens, not confirmations: the v1.2.0 points are
single 15-second runs per rate on the 48-core frontend, and the v1.1.0 points
single 15-second (48 cores) and 20-second (96 cores) runs per rate on the
16-core frontend. With only 500 and 1,000/s measured for v1.1.0, its true limit
lies between them. Counting only runs whose frontend was not the limit, the
highest completion rates under overload compare throughput more closely: 1,983
against 599 per second on 48 cores (3.31 times) and 3,386 against 825 per
second on 96 cores (4.10 times).

At 1,000 requests/s, one 96-core server and two 48-core servers each gave p99
33.7–34.1 ms with every timed request within one second in three 20-second
runs. In the earlier v1.1.0 campaign, the single 96-core server accepted 27–32%
within one second at that rate while the two 48-core servers met it.

At 500 requests/s for 900 seconds on the 48-core VM, all 450,000 timed requests
were accepted within one second, with p50 25.6 ms, p99 33.4 ms and maximum
34.0 ms, against p99 267.0 ms and maximum 307.1 ms for v1.1.0 in the earlier
campaign.

### Overload and server memory

Two 60-second runs offered more than the one-connection limit to the 192-core
server in continuous mode. At 5,100 requests/s with the server process limited
to 2,760 MiB of memory and no swap, the server's sampled peak RSS was
548,064 KiB (535.2 MiB), about 19% of the limit (402,948 KiB or 393.5 MiB by
GNU time), and it exited normally.
Of 306,000 timed requests, 125,769 were accepted and 1.15% of the offered
requests met one second. The server rejected none: the frontend's pending
limit of 8,192 requests equals the server's admission cap, so the excess,
180,231 requests, stopped at the frontend unsent, while the server's return
budget filled to its cap of 192 responses and bounded the finished replies it
held. With the server's sending rate limited to 400 Mbit/s at 3,400
requests/s, the sampled peak RSS was 493 MiB (373 MiB by GNU time); 20,131 of
204,000 timed requests were accepted, 179,756 were not sent and 4,113 sent
requests had no reply by the frontend's 15-second drain limit. The server
rejected no request in that run either.

### Compute cost per million requests

At the highest rate that met one second, the 192-core VM costs about USD 0.87
per million requests with v1.2.0, against USD 2.87 at 1,000/s in the earlier
campaign and at most USD 2.50 at 1,150/s on the same day with v1.1.0. The
same-day value is an upper bound: it comes from one 60-second run at 1,150/s,
and v1.1.0 was not tried at higher rates. The estimate is
the VM's on-demand Linux hourly price, USD 10.34592 for the 192-core instance
type in US East (N. Virginia) on 2026-10-25, divided by the measured rate for
continuous operation. It leaves out the frontend, storage, network transfer
and taxes.

## Prover computation in v1.2.0

### One thread and the worker curve

On the same 192-core C8a bare-metal type as the earlier CPU campaign, at depth
24 and batch 768, v1.2.0 proving-only rates are 7,713.71, 7,220.36 and
5,390.07 inner proofs/s at 192 workers for membership, non-membership and
update, against 3,195.50, 2,947.08 and 2,102.02 for v1.1.0 measured the same
day. At 1, 48, 96 and 192 workers the v1.2.0 rate is 2.53, 2.48, 2.43 and 2.41
times higher for membership, 2.56, 2.52, 2.47 and 2.45 times for
non-membership, and 2.71, 2.68, 2.63 and 2.56 times for update. The same-day
v1.1.0 membership rates came within 0.4% of the earlier campaign at 1 and
192 workers.

A prepared request on one thread took 16.95, 18.22 and 24.62 ms at the median,
against 42.10, 46.10 and 65.03 ms for v1.1.0 on the same day. A fresh request,
which also compiles the circuit and commits to it, took 129.92, 130.98 and
250.09 ms. Within the same runs, reuse therefore lowers per-request latency
7.66, 7.19 and 10.13 times with v1.2.0, against 3.69, 3.46 and 4.45 times in
the earlier v1.1.0 campaign; the same-day v1.1.0 runs measured prepared
requests only. In the five-process output-policy supplement, parallel output
lowers the complete prepared local-batch time 14.64, 14.10 and 14.45 times with
v1.2.0, against 10.71, 9.97 and 9.71 times in the earlier v1.1.0 campaign; the
ratio grew because proving got faster.

### Allocations per proof

In the memory study's mixed two-layer circuit of width 4,096, with one job
pinned to one CPU, one v1.2.0 proof made 85 allocation calls against 1,282 for
the v1.1.0 prover rebuilt and run the same day, and took 1.80 ms against
4.64 ms at the median. At width 65,536 the calls fell from 1,698 to 101 per
proof and the proof time from 79.11 to 28.84 ms. The additional requested
allocation peak and the oracle's owned Vec capacity did not change. Requested
bytes per proof rose from 1,571,688 to 1,710,696 B at width 4,096, as fewer,
larger requests replaced many small ones. Allocation calls, requested bytes,
the requested peak and process RSS are separate measures.

### Build settings

| Build | Membership | Non-membership | Update | Relative to native |
| --- | ---: | ---: | ---: | ---: |
| Default `--release` | 28.18 ms | 30.42 ms | 42.02 ms | 1.66–1.71 |
| `-Ctarget-cpu=x86-64-v3` | 15.26 ms | 16.56 ms | 22.10 ms | 0.90 |
| `-Ctarget-cpu=native` | 16.96 ms | 18.33 ms | 24.63 ms | 1 |

Each value is the median latency of one prepared depth-24 request on one
thread of the 192-core bare-metal host, from one process of 1,000 timed
requests per build and operation. These build comparisons were not repeated,
so the faster x86-64-v3 result on this host is a single-process observation.
The native build uses AVX-512 on this host and the x86-64-v3 build AVX2.

### Proof bytes

Version 1.2.0 proves the same bytes as v1.1.0. In the engine study, the proof
hashes of 768 fixtures per operation at depths 24, 28 and 32, in the native and
the default build, all equal the v1.1.0 hashes: 13,824 comparisons. The memory
study's 284 v1.2.0 proofs match the earlier campaign's hashes, and the serving
runs checked accepted replies against the canonical proofs of the fixed corpus.

## One generic prover: memory and result preservation

Four two-layer families (mixed linear/product, linear, product, and cube/affine)
are tested at eleven power-of-two widths from 4 through 4,096. Each mode has
three separate processes, with one warmup and three timed samples per process:
264 processes, 792 timed observations and 264 warmups. The measured prover is
pinned to CPU 0 on a 48-core VM and runs one job. It is not 48-core throughput.

At mixed width 4,096, medians of the three process medians are:

| Boundary | Test-only Dense | Production Sparse |
|---|---:|---:|
| Requested allocation peak | 1,879,247,872 B | 579,584 B |
| Exposed oracle Vec capacity | 1,610,612,736 B | 508,096 B |
| Whole-process GNU-time RSS | 1,855,016 KiB | 20,736 KiB |
| Observed prover interval | 11,610,216,436 ns | 4,630,590 ns |

The requested-allocation row counts successful additional requested bytes.
The allocation ratio is about 3,242.41 and the process-RSS ratio about 89.46;
they describe different ownership intervals. The canonical field-basis proof
observations match and verification accepts every completed pair. These
observations use benchmark field-basis JSON, separate from `inner-proof-v1`;
Sparse-only scale cases have no completed Dense counterpart. The controlled
contrast does not establish an external-engine ranking.

The v1.2.0 rerun of this campaign on the same VM type gives, for production
Sparse at mixed width 4,096:

| Boundary | v1.1.0, earlier campaign | v1.2.0 |
|---|---:|---:|
| Requested allocation peak | 579,584 B | 579,584 B |
| Exposed oracle Vec capacity | 508,096 B | 508,096 B |
| Whole-process GNU-time RSS | 20,736 KiB | 20,876 KiB |
| Observed prover interval | 4,630,590 ns | 1,797,814 ns |
| Allocation calls per proof | 1,282 | 85 |
| Requested bytes per proof | 1,571,688 B | 1,710,696 B |

The Dense reference code did not change. With v1.2.0 the allocation ratio is
still 3,242.41 and the process-RSS ratio is 88.87; the published 89.46 is the
v1.1.0 measurement.

Allocator counters and stage observation are enabled inside both prover timers.
JSON construction, hashing and verification occur afterwards but remain in
process RSS. Counter overhead is not subtracted. Requested bytes exclude
allocator metadata/slack, stacks and internal transient realloc overlap.
Capacity includes retained buffers after truncation. Whole-process RSS includes
fixtures and logging; differing family fixture representations prevent a
causal cross-family RSS interpretation.

All values and actual stage/cadence observations are preserved. Six detailed
figure families show all process points, empirical distributions, memory
growth, retained capacity, actual RSS traces and telemetry coverage. Short
processes with no sampled telemetry remain identified, rather than interpolated.

## Actual constrained scale and concurrent jobs

The memory-limit study preserves 17 attempts: fourteen successes, one
address-space allocation abort and two native cgroup OOMs. At width 2,048,
Sparse completed 1/2/4/8 independent jobs under a 4-GiB address-space guard;
Dense completed 1/2/4 and aborted at 8. Under the distinct 3-GiB cgroup with
swap disabled, Sparse 4/8 and Dense 4 succeeded; Dense 8 was OOM-killed.
The shared circuit/witness and each job's private oracle/proof are documented.
Actual per-job intervals show overlap without requiring layer lockstep.

Separate active-cap entry records confirm 3 GiB and swap 0 before the scale
cases. Dense width 8,192 was OOM-killed before returning a proof; Sparse widths
8,192/16,384/32,768/65,536 each returned one warmup and three timed proofs.
Width 65,536 is the largest tested point, not a global supported maximum.
An address-space abort, native OOM, unexecuted condition and controller stop
are different dispositions. Missing failure RSS is not manufactured. The
v1.2.0 rerun of all 17 attempts gave the same outcome for each attempt.

## Internal computation: earlier v1.1.0 campaigns

These v1.1.0 results are the reference series for
[Prover computation in v1.2.0](#prover-computation-in-v120). The
[first CPU campaign](../benches/controlled-cpu-2026-10-06/README.md) separates
prepared proving, witness creation, fresh setup, worker counts and depth.
At depth 24/batch 768/192 workers its proving-only rates are
3,207.74/2,930.85/2,092.03 inner proofs/s for membership/absence/update.

The [five-process supplement](../benches/controlled-cpu-2026-10-06-supplement/README.md)
measures direct compile/derive/commitment/witness/prove/encode/verify functions,
same-proof wiring, output parallelization and eight input variants. Its broader
parallel witness→prove→encode→encoded verification rates at the same profile
are 1,593.17/1,431.66/1,167.49 per second. They exclude arrival, networking,
database state and delivery. They are not serving rates.

Prepared reuse saves the full circuit commitment as well as compilation.
Direct depth-24 fresh/prepared measurements use three processes per operation
and mode, each with 1,000 timed requests. Ratios of run-matched process
summaries are approximately 3.69, 3.46 and 4.45 for membership, absence and
update. These are per-request proving-path intervals; encoding, transport and
acceptance are excluded.

The same-proof Table/Derived comparison times the complete prepared typed
`verify_sync_op_with` call, including request validation and native leaf/path
hashing. Only the wiring oracle changes. Circuit, wiring and commitment
preparation, proof generation, encoding and transport are outside the timer.
Across nine depth/operation profiles, the Table/Derived ratio is 10.80–23.68.
Each value is the median of five process summaries, each itself the median of
300 same-proof paired ratios. Table is already a sparse wiring oracle; it is
not the Dense prover memory reference. The verifier did not change in
v1.2.0.

The output-mode ratio 9.71–10.71 applies to depth 24, batch 768 and 192 workers.
It times the complete prepared local batch: witness generation, proving,
encoding and encoded verification. Both policies parallelize witness
generation and proving; only encoding and encoded verification change mode.
Preparation, transport and post-timer hashing/logging are excluded. The range
spans the three operation-specific medians across five processes, each process
summarized by the median of ten paired serial/parallel interval ratios. It is
not the ratio of separately summarized throughput medians. Smaller batches
have their own effects. In the supplement, 327,360 serial/parallel proof-byte
pairs preserve the canonical result.

The compiler produces 118 layers in all nine depth/operation profiles, while
membership encoded bytes increase 2.93% between depths 24 and 32. These existing
results are reused without pooling different hosts or rerunning the earlier
418 processes. Cube/affine fusion has source-structure evidence, not a separate
measured speed multiplier. The nine mechanisms combine measurement, structure,
controls and formal-model evidence rather than nine isolated causal experiments.
The reusable-core benefit also includes selected Rust contract proofs and a
conditional forward acceptance theorem, summarized in the
[refinement review map](refinement.md). Those results help inspect and maintain
acceptance checks; the measured speed and memory improvements are separate
engineering observations.

## Arrival through actual full-proof acceptance: v1.1.0 batch caller

The v1.1.0 thin caller uses independent periodic scheduled arrivals, one FIFO per
operation kind, oldest-ready flushing, a batch cap and a maximum waiting
setting. Each worker processes one compute batch at a time, parallelizes
witness/proof/encoding, then sends the complete encoded proof. The frontend
checks framing, hash and original-request binding and calls the strict encoded
verifier. The measured endpoint is that final acceptance. The reference
server's `original` mode in `benches/serving` reproduces this loop.

Each offered request has a unique identity. Submitted requests retain their
sent, admitted, returned, received and completed chain; explicit pre-send
failures have no server chain. Warmups remain in raw data but are excluded
from timed distributions.
The corpus has 192 fixed fixtures per kind, cycled across repeated proof jobs.
It is not an independently sampled application-input population. The mix below
is membership/absence/update 1:1:1 at depth 24, using a separate 16-core frontend.

All three confirmed settings use a 5-ms maximum batch wait. Their worker count
and batch cap are equal, per worker. The following table keeps the execution
settings separate from the detailed acceptance observations.

| Deployment | Offered requests/s | Workers / cap | Confirmation |
|---|---:|---:|---|
| 48 cores, 96 GiB | 500 | 48 / 48 | One 900-s run |
| Two 48-core, 96-GiB workers | 1,000 total | 48 / 48 each | Three 20-s runs |
| 192 cores, 384 GiB | 1,000 | 192 / 192 | Three 60-s runs |

- **48-core confirmation:** 450,000 timed requests; all within 500 ms and
  95.601333% within 250 ms. p99 267.025246 ms; maximum 307.095548 ms.
- **Two-worker confirmation:** 500 requests/s per worker; all timed requests
  within 500 ms. Process p99 values span 282.108–329.785 ms.
- **192-core confirmation:** all timed requests within one second. The three
  process p99 values are 426.032, 438.775 and 443.471 ms; the corresponding
  fractions within 500 ms are 99.9183%, 99.7167% and 99.6217%.

The last setting meets the one-second comparison budget for every timed request
in those three runs. A separate 1,150/s observation below meets two seconds for
every request while its queue grows. Neither observation is a global GKR
computation limit. Different confirmation periods and hosts remain separate;
two-worker 20-second success is not two-worker 15-minute stability.

The equal-total-resource comparison uses one 96-core worker with batch 96
against two 48-core workers with batch 48 each, with the same 5-ms wait and
frontend. The single 96-core configuration at 1,000/s accumulated queue and
had process p99 2.545–2.752 seconds; it eventually accepted all requests. The
comparison supports the measured deployment policy rather than proving that
every 96-core setting is inferior. Proof traffic is routed once; total encoded
body bytes at the same offered rate are equal across the two topologies.

## Fine tuning, adverse operating points and separate confirmation: v1.1.0

The 48-core fine study preserves nineteen conditions with three processes each,
including workers 32/36/40/44, caps 16/24/32/40/48, waits 1/5/10 ms, rates
250/500/650/750/1,000 and the three single-operation loads. Of 456,750 timed
offers, 451,429 accepted and 5,321 received explicit server-run-limit refusals.
Those refusals remain in success-rate denominators and separate from accepted
latency CDFs. Small batches and insufficient concurrency produce substantial
queue growth. Workers 36–40 and cap 40 are short-run candidates at balanced
500/s, while the 900-second 48/48/5-ms result remains the confirmed baseline.
The update-only 500/s result did not meet the one-second objective in every run.

The 192-core VM study contains 47 actual process pairs: pilot 1, matching 6,
high-load tuning 18, a 50/s-spaced knee study 18, one 1,150/s long confirmation
and three 1,000/s long confirmations. It preserves 1,102,000 timed and 12,032
warmup offers. The 1,114,032 offers equal 1,079,666 sent/accepted requests plus
34,366 explicit pre-send `frontend_max_pending` outcomes. Submitted requests
had no server rejection, loss, duplicate or unresolved response.

The 1,100/1,150/1,200/s studies compare caps 192/384 with all 192 workers.
At 1,150/s/cap 192, all requests in three 15-second runs met one second.
The separate 60-second observation ultimately accepted all 69,000 timed
requests. Of these, 48,553 (70.3667%) met one second and all 69,000 met two
seconds. The maximum latency was 1,598.489 ms and p99 was 1,471.284 ms.
The remaining 20,447 exceeded the one-second comparison budget; they were not
rejected or lost. The 256 warmups are excluded from these denominators.

Pending work grew from 562 at five seconds to 1,559 at 60 seconds, and the final
five-second cohort of 5,750 offers all exceeded one second. At the end of the
input window, 67,441 timed requests were complete; final acceptance occurred at
61.393972789 s. Including that drain gives 1,123.89 accepted requests/s over
the finite completion window. Sixty seconds is the offering duration, not an
engine lifetime or a per-request delay. The queue growth prevents a sustained
1,150/s claim beyond this observation.

This preserves both the useful delivered throughput and the failed one-second
extrapolation from the short screens. The first completed one-second-budget
miss remains in the data; the other two planned repetitions were not executed.
The later 1,000/s confirmations have different phase identities and are
separate observations.

[Performance tuning](https://oraclizer.io/ss-gkr/docs/guides/performance-tuning/)
relates tree depth, memory budget, worker count, batch cap and deployment shape
to these observations.

## Statistics, clocks, observation and scope

The new arrival studies use observed nearest-rank quantiles, at sorted index
`ceil(q*N)-1`, and integer nanoseconds. The earlier CPU campaign retains its
published `floor((N-1)*q)` sample-quantile convention; the two conventions are
not silently unified. The five-process supplement retains type-7 linear
interpolation at `(N-1)*q`, with the ordinary sample median. Memory summaries
retain timed medians per process.
Separate process values and full ranges are displayed; ranges are descriptive,
not confidence intervals. Dense scatter or exact ECDF steps may be rasterized in
vector exports, with all source observations retained. No outlier is removed
and no interpolated operating point is called measured.

Frontend latency uses its local monotonic clock. Original Unix timestamps
locate events; they are not required to equal a difference of monotonic
durations. Actual offered timestamps are preserved rather than reconstructed.
Server queue and compute use that server's own clock. No cross-host timestamp
subtraction is used to manufacture one-way network latency.

Batch timers are shared and counted once. Encoding-to-last-write and between-
batch time include hashing, framing, logging, release and other service work;
their entire sum is not labelled network latency. CPU uses observed tick
differences at HZ 100 over actual telemetry intervals. The 20-ms target cadence
has its full actual distribution; absent observations are not filled. GNU time
and sampled `/proc` RSS remain separately identified when their observations
differ. Logging is measured inside the system/RSS boundary and is not
subtracted to claim counterfactual throughput.

Final deadline outcomes, scanner observations, explicit rejection, pre-send
overflow and connection EOF are separate. Success fractions divide by all
timed offers. A completion-window rate includes drain; acceptance count divided
by scheduled duration can hide queue growth and is not sustainable capacity.
Phase plus run ID and process identity avoids conflating repeated run names.

The v1.2.0 serving runs keep five outcomes for a timed request: accepted
within the budget, accepted late, rejected by the server with a reason string,
not sent because the frontend's pending limit was full, and sent without a
reply by the frontend's drain limit. The last two count as failures in success
fractions and are excluded from accepted-latency quantiles. Continuous mode
has no batch rows; each reply's `job_stages` record carries that job's
dispatch, witness, proof, encoding, hash, release and write times.

These measurements end at inner-proof acceptance. They do not measure a live
database commit, sequential root adoption, consensus, cross-domain settlement
or product finality, and they add no whole-program or Fiat–Shamir assurance.
Plonky3 0.4.3 supplies field, hash and challenger primitives. A bounded
external KoalaBear compatibility check probed the Lambdaworks GKR
implementation. Raw diagnostics remain preserved;
results are selected for their actual contribution to the implementation and
operating questions, with complete validity and provenance disclosed.
