# Stage 5: extracted Haskell and CSV adapter hardening

Stage 5 closes the non-zero-offset Haskell extraction and CSV adapter surface.
The common-layer extraction names and the CSV parser already exist after Stages
2 through 4, so this stage is intentionally a hardening and documentation
stage rather than a new common-interface expansion.

This stage does not add runtime hooks, QEMU behavior, trace semantics, timer
behavior, migration semantics, LLF certificate generation, or a full final
certificate CLI input format.

## Goal

- Treat the offset-aware extraction and CSV runner as the adapter boundary for
  periodic task sets with offsets.
- Preserve legacy 3-column CSV input while supporting 4-column offset input.
- Ensure generated prefix certificates project concrete CSV offsets into the
  extracted offset-aware periodic job model.
- Keep the final feasibility checker surface exportable without pretending that
  the CSV runner can yet consume full `EDFInfiniteCert + sidecar` certificates.

## Public Interface Delta

No new Rocq interface is required in Stage 5.

The following extraction surface is the Stage 5 public interface:

```coq
extracted_periodic_offsets
extracted_offset_window_dbf_test_upto
extracted_offset_window_dbf_counterexample
periodic_conservative_schedulability_decide
periodic_offset_window_schedulability_decide
PeriodicPolicy
check_periodic_policy_feasibility
check_periodic_feasibility_checked_sidecar_extracted
```

`periodic_conservative_schedulability_decide` remains the conservative
zero-origin processor-demand check over extracted periodic tasks. It may reject
some offset-feasible task sets.

`periodic_offset_window_schedulability_decide` is the offset-aware finite-window
cutoff check. It is the CSV adapter's acceptance path for offset-sensitive
processor-demand checks.

Do not add `PeriodicAnalysisMode` in this stage. The final checked-certificate
checker still includes the conservative feasibility guard internally, so a
policy or mode dispatcher would imply a precision that the final checker does
not yet provide.

## CSV Adapter Behavior

The CSV runner accepts these task formats:

```text
cost,period,deadline
cost,period,deadline,offset
```

The 3-column form is legacy-compatible and means `offset = 0`. The 4-column
form requires a nonnegative offset. Costs, periods, and deadlines remain
positive.

The default command:

```sh
scripts/periodic_edf_schedulability_csv TASKS.csv
```

uses the conservative schedulability alias.

The offset-window commands:

```sh
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS.csv
scripts/periodic_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS.csv
```

use the offset-aware DBF interface.

The prefix command remains prefix-only:

```sh
scripts/periodic_edf_schedulability_csv --check-prefix-cert TASKS.csv
```

It must generate releases as:

```haskell
parsedOffset task + jobIndex * parsedPeriod task
```

and size the prefix horizon as:

```haskell
maximum offsets + 2 * hyperperiod tasks + maximum deadlines
```

This command checks the generated finite prefix against extracted offset-aware
periodic jobs. It is not a final feasibility checker and does not consume an
`EDFInfiniteCert + sidecar` input.

## Regression Coverage

Stage 5 keeps the existing CSV coverage for:

- zero-offset legacy CSV input,
- nonzero-offset CSV input,
- overload witnesses,
- negative offset rejection,
- invalid offset-window horizon arguments,
- cutoff-mode acceptance for a tiny task set,
- an offset-sensitive task set rejected by the conservative alias and accepted
  by the offset-window cutoff alias.

It also adds a nonzero-offset prefix-certificate regression:

```csv
cost,period,deadline,offset
2,5,5,2
1,4,3,0
```

The prefix check must accept this fixture, which exercises both the generated
release offset and the offset-expanded prefix horizon.

## Acceptance Checks

Rocq and extraction:

```sh
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtraction.vo
make -C scheduling_theory extract-periodic-edf-sched-hs
rg -n "extracted_periodic_offsets|extracted_offset_window_dbf_test_upto|check_periodic_policy_feasibility" scheduling_theory/extracted/haskell/PeriodicEDFSchedulability.hs
```

CSV regression:

```sh
make -C scheduling_theory test-periodic-edf-sched-csv
```

Repository hygiene:

```sh
git -C scheduling_theory diff --check
git -C scheduling_theory status --short
```

## Out of Scope

- `PeriodicAnalysisMode`.
- A policy-selecting final feasibility dispatcher.
- Full final-certificate CLI input.
- LLF-specific certificate generation.
- Runtime hooks, traces, dispatch, timers, migration, and OS events.
- Stage 6 example suites such as `PeriodicOffsetExamples.v`.

## Known Dirty Files to Avoid

`scripts/test.csv` is an existing untracked file and is not part of Stage 5.
