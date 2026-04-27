# Stage 2 v2: public exposure of pure offset-window cutoff analysis

Stage 2 v1 introduced a finite-horizon offset-aware window-DBF analyzer whose
horizon is supplied by the caller. The pure Stage 2 cutoff theorem then proved
that a conservative finite cutoff is sufficient for arbitrary windows. Stage 2
v2 exposes that proof-facing theorem through stable public entry points while
keeping the finite-horizon API available as a bounded analyzer.

This plan is limited to the common analysis layer and its extraction / adapter
surface. It does not change final certificates, runtime dispatch behavior,
timer behavior, migration behavior, interrupt handling, scheduler traces, or
OS-specific event semantics.

## Goal

Expose the already-proved pure cutoff path as a stable public interface:

- keep Stage 2 v1 finite-horizon APIs as bounded checks;
- add extraction-facing cutoff APIs for arbitrary-window offset DBF validity;
- make CLI modes distinguish finite-horizon checking from cutoff-backed global
  checking;
- keep Stage 1 scalar DBF decision and witness behavior unchanged.

The abstract interface being preserved is offset-aware periodic window demand:
for every window `[t1,t2]`, the DBF induced by task parameters and offsets must
not exceed the window length.

## Glossary

- **Finite horizon**: a bounded check over windows satisfying `t2 <= H`, where
  `H` is supplied by the caller.
- **Pure cutoff theorem**: the arbitrary-window theorem using only the
  offset-window cutoff check, not the Stage 1 classical scalar DBF guard.
- **Public exposure**: extracted functions, CLI modes, and adapter-facing
  documentation intended for downstream callers.
- **Counterexample witness**: an `option (Time * Time)` identifying an
  overloaded window `(t1,t2)`. This is distinct from the Stage 1 scalar
  `option Time` witness.

## Relationship to Stage 2 v1

Stage 2 v1 is the finite analyzer:

- interface: `extracted_offset_window_dbf_test_upto ts H`, finite
  counterexample search, and bounded `ok_upto`;
- caller obligation: choose a nonnegative horizon `H`;
- soundness claim: overloaded offset-aware windows are checked only for
  `t2 <= H`;
- non-claim: v1 alone does not provide an infinite schedulability guarantee.

Stage 2 v2 must not remove this API. It remains useful for bounded debugging,
smoke tests, and adapter-level diagnostics.

## Relationship to the Pure Cutoff Theorem

The pure cutoff theorem is common-layer proof work. It defines offset-aware
periodic window demand, a conservative cutoff bound, and a soundness theorem
showing that checking windows up to that cutoff implies arbitrary-window DBF
validity.

Stage 2 v2 is not new theorem work. It makes the now-proven theorem available
through stable names, extraction, CLI plumbing, witness output, and documentation
synchronization.

The cutoff bound is conservative. Minimality or tightness is intentionally not
part of the public contract.

## Public Interface Delta

### `PeriodicEDFExtractionDecision.v`

Add extraction-facing definitions for the global cutoff-backed path:

```coq
Definition extracted_offset_window_dbf_cutoff_bound
    (ts : list ExtractedPeriodicTask) : Time :=
  offset_window_dbf_cutoff_bound
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts).

Definition extracted_offset_window_dbf_test_by_cutoff
    (ts : list ExtractedPeriodicTask) : bool :=
  offset_window_dbf_test_by_cutoff
    (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts)
    (enumT_of_extracted_list ts).

Definition extracted_offset_window_dbf_counterexample_by_cutoff
    (ts : list ExtractedPeriodicTask) : option (Time * Time) :=
  extracted_offset_window_dbf_counterexample
    ts
    (extracted_offset_window_dbf_cutoff_bound ts).

Definition extracted_offset_window_dbf_decide_by_cutoff
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_taskset_wf ts
  && extracted_offset_window_dbf_test_by_cutoff ts.
```

Add the global proof-facing property:

```coq
Definition extracted_offset_window_dbf_ok_global
    (ts : list ExtractedPeriodicTask) : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window
      (tasks_of_extracted_list ts)
      (offset_of_extracted_list ts)
      (enumT_of_extracted_list ts)
      t1 t2 <= t2 - t1.
```

Add soundness lemmas:

```coq
Theorem extracted_offset_window_dbf_test_by_cutoff_sound :
  forall ts,
    extracted_taskset_wf ts = true ->
    extracted_offset_window_dbf_test_by_cutoff ts = true ->
    extracted_offset_window_dbf_ok_global ts.

Lemma extracted_offset_window_dbf_decide_by_cutoff_true_ok :
  forall ts,
    extracted_offset_window_dbf_decide_by_cutoff ts = true ->
    extracted_offset_window_dbf_ok_global ts.

Lemma extracted_offset_window_dbf_counterexample_by_cutoff_sound :
  forall ts t1 t2,
    extracted_offset_window_dbf_counterexample_by_cutoff ts = Some (t1, t2) ->
    t2 - t1 <
      taskset_periodic_dbf_window
        (tasks_of_extracted_list ts)
        (offset_of_extracted_list ts)
        (enumT_of_extracted_list ts)
        t1 t2.
```

The proof bridge must derive period positivity on `enumT_of_extracted_list ts`
from `extracted_taskset_wf ts = true`, then apply
`offset_window_dbf_check_by_cutoff`.

### `PeriodicEDFExtraction.v`

Add only the new pure infinite offset-window API names to the extraction list:

```coq
extracted_offset_window_dbf_cutoff_bound
extracted_offset_window_dbf_test_by_cutoff
extracted_offset_window_dbf_counterexample_by_cutoff
extracted_offset_window_dbf_decide_by_cutoff
```

Do not remove Stage 1 scalar DBF exports or Stage 2 finite-horizon exports.

## Observable Results and Witnesses

The common checker produces boolean decisions and, for failures, overloaded
window witnesses `(t1,t2)`.

The adapter-facing CLI should expose two offset-window modes:

```text
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS.csv
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS.csv
```

The finite mode uses the existing extracted finite API:

```haskell
EDF.extracted_offset_window_dbf_decide input (toNat h)
EDF.extracted_offset_window_dbf_counterexample input (toNat h)
```

The cutoff mode uses the new global API:

```haskell
EDF.extracted_offset_window_dbf_decide_by_cutoff input
EDF.extracted_offset_window_dbf_counterexample_by_cutoff input
```

Both modes keep the CSV schema `cost,period,deadline[,offset]`; missing offset
means `0`. A negative offset is invalid input.

Failure output should name both witness endpoints:

```text
window DBF overload witness t1=... t2=...
```

The existing default mode remains unchanged: `TASKS.csv` still uses
`EDF.edf_schedulability_decide`, the Stage 1 scalar/global DBF path. Its scalar
witness shape must not be mixed with offset-window witnesses.

## Common-Layer Obligations

The common layer must:

- define the offset-aware periodic window demand interface locally;
- define the conservative cutoff bound;
- prove that the cutoff check implies arbitrary-window DBF validity;
- expose extraction-facing names whose semantics match the theorem;
- preserve the finite-horizon API as a bounded analyzer;
- avoid encoding runtime queues, dispatch events, trace events, interrupt
  timing, or migration behavior into the common interface.

Runtime details intentionally not part of this interface include task wakeups,
run queues, CPU selection, actual dispatch order, timer latency, and trace log
format.

## Downstream Adapter Obligations

Adapters must:

- choose how concrete callers provide task lists and offsets;
- validate CLI horizons for finite mode as nonnegative integers;
- pass 3-column CSV rows as zero-offset tasks and 4-column rows as explicit
  offset tasks;
- reject malformed rows and negative offsets before invoking the checker;
- interpret boolean results and `(t1,t2)` witnesses without treating them as
  runtime scheduling traces;
- document whether a call is finite-horizon or cutoff-backed global analysis.

The runtime may call a generated checker, but the theorem's common interface is
only about periodic task parameters, offsets, finite windows, and DBF bounds.
Runtime dispatch behavior is outside this common interface.

## Runtime Non-Goals

Stage 2 v2 does not add concrete runtime obligations:

- no final certificate checker changes;
- no arbitrary-offset completion transport changes;
- no scheduler trace changes;
- no runtime hook, timer, interrupt, dispatch, or migration semantics;
- no Awkernel QEMU behavior changes;
- no claim that runtime execution order itself is verified by this checker.

## Implementation Order

1. Add cutoff-backed extracted definitions and soundness lemmas to
   `PeriodicEDFExtractionDecision.v`.
2. Update `PeriodicEDFExtraction.v` to export the new cutoff-backed names.
3. Rebuild the Rocq files for offset cutoff, extraction decision, and extraction.
4. Regenerate `extracted/haskell/PeriodicEDFSchedulability.hs`.
5. Add finite CLI mode
   `--check-offset-window-dbf H TASKS.csv` using the existing finite API.
6. Add cutoff CLI mode
   `--check-offset-window-dbf-cutoff TASKS.csv` using the new global API.
7. Update usage text beside `--check-prefix-cert`.
8. Add local CLI tests and a Makefile/local test target near
   `build-periodic-edf-sched-csv`.
9. Update `stage2.md` summary text if it still describes the cutoff-backed
   public exposure as future theorem work.

## Acceptance Checks

Rocq:

```sh
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicOffsetWindowCutoff.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtraction.vo
```

Extraction:

```sh
make -C scheduling_theory extract-periodic-edf-sched-hs
rg -n "extracted_offset_window_dbf_.*cutoff" scheduling_theory/extracted/haskell/PeriodicEDFSchedulability.hs
```

CLI:

```sh
make -C scheduling_theory scripts/periodic_edf_schedulability_csv
scheduling_theory/scripts/periodic_edf_schedulability_csv TASKS_ZERO_OFFSET.csv
scheduling_theory/scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS_ZERO_OFFSET.csv
scheduling_theory/scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS_NONZERO_OFFSET.csv
scheduling_theory/scripts/periodic_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS_NONZERO_OFFSET.csv
```

Required fixtures:

- positive zero-offset fixture where default mode and finite offset-window mode
  both succeed;
- positive nonzero-offset fixture proving offsets pass through the extracted
  window DBF surface;
- negative nonzero-offset fixture where the checker fails and prints both
  `t1` and `t2`;
- horizon parsing cases: missing `H`, nonnumeric `H`, negative `H`, missing CSV
  path;
- CSV compatibility cases: 3-column rows default offset to `0`, 4-column rows
  parse offsets, negative offsets fail.

Repository hygiene:

```sh
git -C scheduling_theory diff --check
git -C scheduling_theory status --short --untracked-files=all
```

## Open Risks

- The cutoff-backed checker may be expensive because the cutoff is conservative.
- CLI names must keep finite and global modes visibly distinct; otherwise a
  caller may mistake a bounded diagnostic for an infinite guarantee.
- The extracted Haskell names may differ after regeneration; the implementation
  should verify generated identifiers before wiring the CLI.
- Documentation must avoid describing Stage 2 v2 as theorem work. The theorem is
  already present; v2 is exposure, naming, extraction, CLI plumbing, stable
  witness shape, and documentation synchronization.

## Known Dirty Files to Avoid

The following pre-existing changes are outside this plan and should not be
touched by the Stage 2 v2 implementation unless a later task explicitly asks for
them:

```text
plan/EDFInfinite_Haskell.md
plan/stage1.md
plan/non_zero_offset.md
scripts/test.csv
```

Top-level `git_push.sh`, `memo.txt`, and `target/...` are also outside this
plan.
