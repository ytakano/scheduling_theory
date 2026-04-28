# Release Jitter Implementation Roadmap

This roadmap promotes the existing `TaskModels/Jitter/*` layer from
finite-witness wrappers to reusable infinite-time EDF analysis and later LLF /
checker-facing extensions.

The immediate target is release-jitter schedulability theory.  The trace and
witness pipeline described in `plan/schedulability_witness.md` is a future
extension and is not part of the current implementation batch.

---

## 1. Semantic assumptions

- Release jitter belongs to the task-generation layer.  Do not add jitter to
  `Task`, `Job`, or `Schedule`.
- The intended release model is:

  ```text
  nominal_release(τ, k) = offset τ + k * period τ
  nominal_release(τ, k) <= actual_release
  actual_release <= nominal_release(τ, k) + jitter τ
  ```

- Deadlines remain actual-release based:

  ```text
  job_abs_deadline = job_release + task_relative_deadline
  ```

- The current model is delayed release jitter, not early release jitter and not
  nominal-deadline jitter.  If nominal-deadline jitter is needed later, introduce
  a separate task model instead of overloading `JitteredPeriodicTasks.v`.
- Arbitrary jitter does not imply hyperperiodic actual releases.  Hyperperiod
  transport may be used only for nominal-release / bound-level DBF facts unless
  a separate patterned-jitter certificate is introduced.
- Jitter alone does not imply `sporadic_separation_on`.  Any sporadic-model
  bridge that needs separation must keep it as an explicit downstream
  assumption.

---

## 2. Required observable events

No new observable event is required in the common Rocq scheduling layer for the
current release-jitter implementation.

For future `plan/schedulability_witness.md` integration, keep the theory
compatible with an adapter-level event vocabulary containing:

- `job_release`
- `dispatch`
- `preempt`
- `job_complete`
- `dbf_window_checkpoint`

These events should be introduced later in operational / adapter / checker
layers.  They should not be required by `TaskModels/Jitter`, and they should not
change the core `Schedule` interface.

The future witness checker should consume actual releases and task metadata.
It should not reconstruct actual releases from `(task_id, index)` alone.

---

## 3. Interface delta

### PR 1: Semantics, codec, and prefix candidates

Strengthen the existing release-jitter semantics before adding deeper analysis.

Primary files:

- `theories/TaskModels/Jitter/ReleaseJitter.v`
- `theories/TaskModels/Jitter/JitteredPeriodicTasks.v`
- `theories/TaskModels/Jitter/JitteredPeriodicCodec.v`
- `theories/TaskModels/Jitter/JitteredPeriodicInfiniteJobset.v`
- `theories/TaskModels/Jitter/JitteredPeriodicPrefixCoherence.v`

Required interface:

- public lower / upper release lemmas for `within_jitter`
- public generated-job deadline and cost lemmas
- zero-jitter compatibility with periodic generation
- a job-identity codec from `(TaskId, index)` to `JobId`
- infinite candidates-before definitions for generated schedules

The codec is only an identity codec.  Actual release is always read from
`jobs : JobId -> Job`.

### PR 2: Jittered window DBF

Add the window-demand layer that infinite EDF will consume.

Primary file:

- `theories/TaskModels/Jitter/JitteredPeriodicWindowDemandBound.v`

Required interface:

- `jittered_periodic_jobset_deadline_between`
- `jittered_index_may_be_in_window`
- `jittered_index_may_be_in_window_b`
- `jittered_periodic_dbf_window`
- `taskset_jittered_periodic_dbf_window`

The boolean window test should be based on interval intersection:

```text
[nominal, nominal + jitter] ∩ [t1, t2 - relative_deadline] is nonempty
```

This is the important semantic distinction from the current deadline-bounded
finite-horizon DBF.  A job with nominal release before `t1` may still have an
actual release inside `[t1, t2]` because of jitter.

### PR 3: EDF finite and infinite bridges

Connect the jittered window DBF layer to EDF schedulability.

Primary files:

- `theories/TaskModels/Jitter/JitteredPeriodicEDFWindowBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFInfiniteBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFAnalysisEntryPoints.v`

Required interface:

- finite-horizon EDF feasibility from jittered window DBF
- generated EDF schedule using jittered candidates-before
- infinite-time schedulability wrapper using prefix coherence and the existing
  busy-prefix / no-carry-in bridge style

The public theorem should follow the periodic naming style and expose a
window-DBF entry point such as:

```coq
jittered_periodic_edf_schedulable_by_window_dbf_on
```

Do not use completion transport for arbitrary actual jitter.

### PR 4: Cutoff checker

Add a concrete-analysis layer after the semantic DBF bridge is stable.

Primary files:

- `theories/TaskModels/Jitter/JitteredPeriodicOffsetWindowCutoff.v`
- `theories/TaskModels/Jitter/JitteredPeriodicConcreteAnalysis.v`

Required interface:

- conservative cutoff, initially `periodic_offset_window_cutoff + max_jitter`
- bounded boolean checker for jittered window DBF obligations
- counterexample-producing helper for the first overloaded window
- soundness theorem from checker success to the full window-DBF obligation

Hyperperiod shift lemmas should be stated for the may-be-in-window DBF bound,
not for actual release sequences.

### PR 5: Extraction-facing checker API

Add extraction types without changing existing periodic extraction records.

Primary files:

- `theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionTypes.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionDecision.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFExtractionSoundness.v`
- `theories/TaskModels/Jitter/JitteredPeriodicEDFExtraction.v`

Required interface:

```coq
Record ExtractedJitteredPeriodicTask := {
  ejp_cost : nat;
  ejp_period : nat;
  ejp_relative_deadline : nat;
  ejp_offset : nat;
  ejp_release_jitter : nat;
}.
```

Also add a zero-jitter coercion from extracted periodic tasks to extracted
jittered-periodic tasks.

The top-level decision procedure should be a small wrapper over the cutoff
checker.  Its soundness theorem should initially expose codec, finite
generation, candidate coherence, and busy-prefix obligations explicitly before
being wrapped into a more convenient final theorem.

### PR 6: LLF extension

After EDF is stable, add LLF infinite schedulability wrappers.

Primary files:

- `theories/TaskModels/Jitter/JitteredPeriodicLLFInfiniteBridge.v`
- `theories/TaskModels/Jitter/JitteredPeriodicLLFAnalysisEntryPoints.v`

LLF should reuse:

- jittered generation semantics
- jittered codec
- jittered candidates-before / prefix coherence
- jittered window DBF

Only the policy bridge and finite-to-infinite lift should be LLF-specific.

### PR 7: Examples and tutorials

Add examples only after the relevant public theorem is stable.

Suggested files:

- `theories/Examples/JitteredPeriodicEDFExamples.v`
- `theories/Examples/JitteredPeriodicInfiniteEDFExamples.v`
- `theories/Examples/JitteredPeriodicOffsetJitterDBFExamples.v`
- `theories/Examples/JitteredPeriodicZeroJitterCompatExamples.v`
- `theories/Examples/JitteredPeriodicLLFExamples.v`
- `theories/Tutorials/JitteredEDFInfiniteSchedulability.v`
- `theories/Tutorials/JitteredLLFInfiniteSchedulability.v`

Minimum regression scenarios:

- `jitter = 0` agrees with periodic EDF.
- `offset <> 0, jitter = 0` agrees with offset-periodic window DBF.
- `offset <> 0, jitter > 0` exercises the new jittered window DBF checker.
- EDF finite and infinite wrappers are consumed by concrete examples.
- LLF finite and later infinite wrappers consume the same jittered jobset layer.

---

## 4. Proof obligations

### Semantics and compatibility

- `within_jitter_refl_zero`
- `within_jitter_actual_ge_nominal`
- `within_jitter_actual_le_nominal_plus_jitter`
- `generated_by_jittered_periodic_release_lb`
- `generated_by_jittered_periodic_release_ub`
- `generated_by_jittered_periodic_deadline_eq`
- `generated_by_jittered_periodic_cost_le`
- `generated_by_jittered_periodic_zero_jitter_iff_periodic`

### Codec and candidates

- codec soundness for every in-scope `(τ, k)`
- codec completeness for generated jittered-periodic jobs
- codec injectivity or an equivalent uniqueness property sufficient for
  enumeration and candidate proofs
- candidates-before soundness
- candidates-before completeness
- candidates-before `NoDup`
- candidates-before prefix monotonicity

### Window DBF

- boolean reflection for `jittered_index_may_be_in_window_b`
- actual window workload bounded by per-task jittered window DBF
- aggregate actual window workload bounded by taskset jittered window DBF
- zero-jitter equality with periodic window DBF
- monotonicity in the right endpoint
- antitonic / weakening behavior in the left endpoint, stated in the form most
  useful for existing processor-demand proofs
- permutation, append, and `NoDup` stability for taskset DBF aggregation

### EDF bridge

- finite-horizon window DBF implies finite EDF feasibility under the existing
  bridge-side assumptions
- generated EDF finite prefix agrees with infinite generated EDF on the prefix
- busy-prefix / no-carry-in bridge discharges the required finite prefixes
- infinite EDF no-deadline-miss from the jittered window DBF condition
- `schedulable_by_on` wrapper for generated jittered-periodic EDF

### Cutoff and concrete checker

- jittered DBF may-be-in-window bound shifts by hyperperiod
- conservative cutoff covers all critical windows
- boolean checker success implies all checked windows satisfy DBF <= supply
- cutoff theorem lifts bounded checker success to all windows
- counterexample helper is sound when it returns a window

### Extraction soundness

- extracted task record maps to semantic task parameters
- zero-jitter coercion preserves the periodic interpretation
- decision procedure soundness for EDF, first with explicit side obligations
- final EDF soundness wrapper after the bridge assumptions are packaged

### LLF

- reuse the jittered finite-horizon witness lift already available for LLF
- prove generated LLF prefix coherence over the jittered candidate source
- prove infinite LLF schedulability from the same jittered window DBF premise

---

## 5. Risks for the Rust design

- Do not encode release jitter as scheduler policy state.  Rust should expose
  actual releases and task metadata; the proof layer interprets them through
  task generation.
- Do not assume arbitrary jitter traces repeat with the hyperperiod.  A
  patterned-jitter certificate is a separate future feature.
- Do not emit nominal-release deadlines for this model.  The current Rocq
  semantics uses actual-release deadlines.
- Keep job identity stable independently from actual release reconstruction.
  `(task_id, index)` may identify the job, but it does not determine actual
  release.
- Keep trace timestamp normalization and SV-COMP-style YAML / GraphML witness
  generation out of this implementation batch.  Those should target the
  checker-facing DBF interfaces added here.
- Avoid Rust-side artifacts that require runtime-specific observables in the
  common proof layer.  Adapter-local evidence should discharge downstream
  obligations instead.


---

## Progress

Update this document after implementing.

- PR 1 started and implemented:
  - added release-jitter public compatibility lemmas
  - added `JitteredPeriodicInfiniteJobset.v`
  - added `JitteredPeriodicCodec.v`
  - extended `JitteredPeriodicEnumeration.v` with finite and before-time
    enumeration for jittered periodic jobs
  - added `JitteredPeriodicPrefixCoherence.v`
  - registered the new files in `_CoqProject`
- Verification:
  - targeted jitter files compile
  - downstream jitter EDF / LLF bridge files compile
  - full `make -j2` passes
- PR 2 started and implemented:
  - added `JitteredPeriodicWindowDemandBound.v`
  - added jittered window jobset and interval-intersection index predicate
  - added per-task and taskset DBF window demand bounds
  - added zero-jitter compatibility with periodic window DBF
  - added endpoint monotonicity lemmas for jittered window DBF
  - registered the new file in `_CoqProject`
- Verification:
  - `JitteredPeriodicWindowDemandBound.v` compiles
  - downstream jitter EDF / LLF bridge files compile
  - full `make -j2` passes
- PR 3 started:
  - added jittered EDF window bridge entry points
  - added generated jittered EDF schedule definitions
  - added generated jittered EDF scheduler relation and validity lemmas
  - exposed the infinite window-DBF schedulability wrapper with explicit
    finite-prefix feasibility / no-carry-in obligations
  - registered the new files in `_CoqProject`
- PR 3 continued:
  - added jittered EDF processor-demand bridge lemmas for finite horizons
  - finite generated-EDF schedulability now derives `feasible_on` from
    `taskset_jittered_periodic_dbf_window` and the no-carry-in bridge
  - infinite generated-EDF schedulability no longer requires an explicit
    `feasible_schedule_on` premise
  - infinite generated-EDF schedulability now keeps finite/infinite
    `agrees_before` prefix coherence as an explicit proof obligation
  - full automatic finite/infinite prefix coherence remains the next PR3 task
- PR 3 continued:
  - added `JitteredPeriodicEDFPrefixCoherence.v`
  - proved finite-horizon / infinite generated EDF prefix coherence for
    jittered candidates-before
  - internalized the finite/infinite `agrees_before` obligation in
    `jittered_periodic_edf_schedulable_by_window_dbf_on`
  - kept the no-carry-in busy-prefix bridge explicit as the remaining
    analysis-side PR3 obligation
- PR 4 started:
  - added `JitteredPeriodicConcreteAnalysis.v`
  - added bounded boolean checking for jittered window DBF obligations
  - added a sound first-overloaded-window helper for bounded checks
  - added `JitteredPeriodicOffsetWindowCutoff.v`
  - added conservative cutoff surface
    `offset_window_dbf_cutoff_bound + max_jitter`
  - proved cutoff-bounded checker soundness for windows with `t2` below the
    conservative cutoff
  - added hyperperiod-shift lemmas for the jittered may-be-in-window DBF bound
  - proved taskset jittered window DBF equality under post-jitter-offset
    hyperperiod shifts
  - added a post-jitter-offset shifted cutoff theorem that transports bounded
    checker success to shifted windows
  - added periodic-to-jittered DBF inclusion lemmas for cutoff load arguments
  - added a jitter-aware one-hyperperiod growth bound after each task's
    relative deadline is already covered by the window
  - proved successful jittered cutoff checking implies
    `hyperperiod_load <= periodic_hyperperiod`
  - proved full all-window cutoff soundness via
    `jittered_offset_window_dbf_check_by_cutoff`
- Verification:
  - `JitteredPeriodicEDFWindowBridge.v` compiles
  - `JitteredPeriodicEDFInfiniteBridge.v` compiles
  - `JitteredPeriodicEDFAnalysisEntryPoints.v` compiles
  - downstream jitter EDF / LLF bridge files compile
- PR 6 started:
  - added `JitteredPeriodicLLFPrefixCoherence.v`
  - added `JitteredPeriodicLLFInfiniteBridge.v`
  - added `JitteredPeriodicLLFAnalysisEntryPoints.v`
  - registered the new LLF bridge/analysis files in `_CoqProject`
- PR 6 continued:
  - LLF finite/infinite generated schedules are defined and share a common
    jittered candidate source
  - finite DBF obligations are lifted to an infinite LLF schedulability theorem
  - finite-to-infinite prefix coherence for generated LLF schedules is internalized
  - `_CoqProject` registration for new LLF files completed
- PR 6 continued:
  - `JitteredPeriodicLLFPrefixCoherence.v`, `JitteredPeriodicLLFInfiniteBridge.v`,
    and `JitteredPeriodicLLFAnalysisEntryPoints.v` compile
- PR 5 started:
  - added `JitteredPeriodicEDFExtractionTypes.v`
  - added extraction-facing jittered task records and list-to-semantic-task
    adapters
  - added zero-jitter coercion from extracted periodic tasks to extracted
    jittered-periodic tasks
  - added `JitteredPeriodicEDFExtractionDecision.v`
  - exposed cutoff-bound, decision, and counterexample wrappers over the
    jittered offset-window DBF cutoff checker
  - added `JitteredPeriodicEDFExtractionSoundness.v`
  - proved decision success implies the global jittered window-DBF obligation
  - exposed EDF schedulability soundness with codec, nonblocking, and
    no-carry-in bridge obligations explicit
  - added `JitteredPeriodicEDFExtraction.v` for Haskell extraction of the new
    checker surface
- PR 5 continued:
  - added tracked Haskell extraction output
    `extracted/haskell/JitteredPeriodicEDFSchedulability.hs`
  - added `scripts/jittered_edf_schedulability_csv.hs` as a cutoff-checker CLI
    over the extracted jittered EDF API
  - accepted CSV task rows with `cost,period,deadline[,offset[,jitter]]`
  - kept generated CLI binaries ignored
- Verification:
  - `JitteredPeriodicEDFExtraction.v` compiles
  - jittered CSV harness builds with GHC against the extracted Haskell module
  - zero-jitter, offset-only, release-jitter, and invalid-input CSV cases were
    exercised through the CLI
- PR 7 started:
  - added a concrete offset-plus-jitter window DBF checker example
  - added a zero-jitter compatibility example against periodic window DBF
  - added infinite jittered EDF and LLF examples that consume the public
    window-DBF entry points
  - kept codec, nonblocking, and busy-prefix/no-carry-in obligations explicit
    at the example boundary
- Verification:
  - `JitteredPeriodicOffsetJitterDBFExamples.v` compiles
  - `JitteredPeriodicZeroJitterCompatExamples.v` compiles
  - `JitteredPeriodicInfiniteEDFExamples.v` compiles
  - `JitteredPeriodicLLFExamples.v` compiles
