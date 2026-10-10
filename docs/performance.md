# Performance and measured operating profiles

Version 1.1.1 is a BSL distribution and package-metadata revision. The Rust
kernel and formal sources retain their recorded contents. The root Cargo
license field is the sole change in the identity-source selection. The
[licensing distribution record](../release/v1.1/LICENSING_DISTRIBUTION.json)
separates that source comparison from the historical v1.1 executable and
proof. The current metadata revision has not completed an exact compiled
identity reproduction; the historical proof is evidence of its recorded
program only.

The evaluation asks three different questions: how much memory one layer's
prover owns, how quickly an internal computation completes, and which actual
arrival load reaches cryptographic acceptance within a stated latency budget.
These intervals have separate data and units. The [architecture guide](architecture.md)
connects the results to nine implementation benefits; [usage](usage.md)
describes their application conditions.
The [replay guide](../benches/controlled-capacity-2026-10-07/README.md) contains
actual small-control commands. The [dataset locator](../benches/controlled-capacity-2026-10-07/DATASET_LOCATOR.json)
defines the complete raw/table/figure layout and its current preparation status.
The separate engineering manuscript and new dataset are prepared for review,
not newly published records. The locator's publication URL, dataset DOI and
archive digest remain null; the existing software DOI and formal-paper arXiv
identifier do not identify this new dataset or engineering manuscript.

All studies use the immutable v1.1.0 kernel. The earlier two C8a baremetal
campaigns contain 243 and 175 distinct process executions on different hosts.
The later controlled study uses actual C8a 48/96/192-core VMs, fixed corpora,
separate frontend verification, generic same-driver memory contrasts and
bounded memory-limit tests. Changing a worker count on a large VM is separately
labelled and is not a measurement of a smaller machine.

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
are different dispositions. Missing failure RSS is not manufactured.

## Internal computation: preserved earlier campaigns

The [first CPU campaign](../benches/controlled-cpu-2026-10-06/README.md) separates
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
not the Dense prover memory reference.

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

## Arrival through actual full-proof acceptance

The thin caller uses independent periodic scheduled arrivals, one FIFO per
operation kind, oldest-ready flushing, a batch cap and a maximum waiting
setting. Each worker processes one compute batch at a time, parallelizes
witness/proof/encoding, then sends the complete encoded proof. The frontend
checks framing, hash and original-request binding and calls the strict encoded
verifier. The measured endpoint is that final acceptance.

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

## Fine tuning, adverse operating points and separate confirmation

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

These measurements end at inner-proof acceptance. They do not measure a live
database commit, sequential root adoption, consensus, cross-domain settlement
or product finality, and they add no whole-program or Fiat–Shamir assurance.
The bounded external KoalaBear compatibility check did not establish a fair
large-scale external-engine comparison. Plonky3 0.4.3 supplies field, hash and
challenger primitives; it is not the external GKR baseline. The separately
probed external GKR implementation was Lambdaworks. Raw diagnostics remain preserved;
results are selected for their actual contribution to the implementation and
operating questions, with complete validity and provenance disclosed.
