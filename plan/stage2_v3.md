# Stage 2 v3: schedulability-facing aliases and offset-value regression

Stage 2 v2 exposed the pure cutoff-backed offset-window checker through
extraction-facing names. Stage 2 v3 stabilizes the public analyzer surface by
adding schedulability-facing aliases and a regression that shows why the
offset-aware path is useful.

This stage remains inside the common analysis, extraction, and adapter layers.
It does not change final certificates, transport soundness, runtime dispatch,
timer behavior, migration behavior, scheduler traces, or OS-specific events.

## Goal

- Keep all Stage 1 and Stage 2 v2 entry points available.
- Add additive public names that distinguish conservative scalar DBF analysis
  from exact offset-window analysis.
- Preserve witness shapes: scalar overloads use `option Time`; offset-window
  overloads use `option (Time * Time)`.
- Add a regression fixture where the conservative scalar path rejects but the
  offset-window cutoff path accepts.

## Public Interface Delta

Add schedulability-facing aliases in `PeriodicEDFExtractionDecision.v`:

```coq
Definition periodic_conservative_schedulability_decide
    (ts : list ExtractedPeriodicTask) : bool :=
  edf_schedulability_decide ts.

Definition periodic_conservative_schedulability_counterexample
    (ts : list ExtractedPeriodicTask) : option Time :=
  edf_schedulability_counterexample ts.

Definition periodic_offset_window_schedulability_cutoff_bound
    (ts : list ExtractedPeriodicTask) : Time :=
  extracted_offset_window_dbf_cutoff_bound ts.

Definition periodic_offset_window_schedulability_decide
    (ts : list ExtractedPeriodicTask) : bool :=
  extracted_offset_window_dbf_decide_by_cutoff ts.

Definition periodic_offset_window_schedulability_counterexample
    (ts : list ExtractedPeriodicTask) : option (Time * Time) :=
  extracted_offset_window_dbf_counterexample_by_cutoff ts.
```

Add proof-facing alias lemmas:

- `periodic_conservative_schedulability_decide_true_global_dbf_ok`
- `periodic_conservative_schedulability_counterexample_sound`
- `periodic_offset_window_schedulability_decide_true_ok`
- `periodic_offset_window_schedulability_counterexample_sound`

Export the aliases in `PeriodicEDFExtraction.v`. Do not remove or rename the
older low-level names.

## Adapter Behavior

The CSV runner keeps the same user-visible modes:

```text
scripts/periodic_edf_schedulability_csv TASKS.csv
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS.csv
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS.csv
```

The default mode should call the conservative aliases. The cutoff mode should
call the offset-window schedulability aliases. The finite-horizon mode remains
the explicit bounded diagnostic path.

## Regression Fixture

Add this task set to the native CSV test target:

```csv
cost,period,deadline,offset
2,5,2,0
2,5,2,2
```

Expected behavior:

- default conservative mode rejects and prints scalar witness `t=2`;
- `--check-offset-window-dbf-cutoff` accepts.

This proves that nonzero offsets can make exact offset-window analysis less
conservative than the scalar DBF path.

## Acceptance Checks

Rocq:

```sh
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtractionDecision.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtraction.vo
```

Extraction:

```sh
make -C scheduling_theory extract-periodic-edf-sched-hs
rg -n "periodic_.*schedulability" scheduling_theory/extracted/haskell/PeriodicEDFSchedulability.hs
```

CLI:

```sh
make -C scheduling_theory test-periodic-edf-sched-csv
```

Repository hygiene:

```sh
git -C scheduling_theory diff --check
git -C scheduling_theory status --short --untracked-files=all
```

## Out of Scope

- Stage 3 final certificate checker zero-offset removal.
- Feasibility alias for final checked sidecar certificates.
- LLF policy-neutral certificate connection.
- Any runtime hook, trace, dispatch, timer, migration, or OS event semantics.
- Renaming or removing existing Stage 1 / Stage 2 v2 exported names.

## Known Dirty Files to Avoid

`scripts/test.csv` is an existing untracked file and is not part of Stage 2 v3.
