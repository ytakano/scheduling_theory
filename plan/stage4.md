# Stage 4: policy-neutral feasibility entry point and LLF connection

Stage 4 introduces a policy-facing analysis layer over the Stage 3 feasibility
checker. The checked certificate remains an EDF-generated feasibility witness.
The policy argument selects the downstream soundness theorem; it does not select
a different boolean checker.

This stage is proof/extraction-facing only. It does not add an LLF certificate
checker, LLF prefix generator, runtime hooks, QEMU behavior, trace semantics,
timer behavior, migration semantics, or OS-specific events.

## Goal

- Expose a policy-neutral boolean checker:
  `check_periodic_policy_feasibility`.
- Add an explicit `PeriodicPolicy` type with `PolicyEDF` and `PolicyLLF`.
- Prove EDF soundness by delegating to the Stage 3 feasibility soundness theorem.
- Prove LLF soundness using the existing LLF any-offset classical DBF theorem
  while keeping the EDF busy-prefix bridge premise explicit.

## Public Interface Delta

Add `PeriodicPolicyAnalysis.v`:

```coq
Inductive PeriodicPolicy :=
| PolicyEDF
| PolicyLLF.

Definition check_periodic_policy_feasibility
    (_p : PeriodicPolicy)
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicFeasibilityCheckedSidecarCert) : bool :=
  check_periodic_feasibility_checked_sidecar_extracted ts cert sidecar.
```

Add `PeriodicPolicyAnalysisEntryPoints.v` with:

- `check_periodic_policy_feasibility_edf_sound`
- `check_periodic_policy_feasibility_llf_sound`

The LLF theorem keeps this premise explicit:

```coq
forall H j,
  periodic_jobset_upto ... H j ->
  job_abs_deadline ... <= H /\
  exists t1 t2,
    busy_prefix_witness ... /\
    periodic_edf_busy_prefix_bridge ...
```

This keeps Stage 4 small and avoids reworking the transport proof layer.

## Implementation Notes

- Register both new files in `_CoqProject`.
- Export `PeriodicPolicy` and `check_periodic_policy_feasibility` from
  `PeriodicEDFExtraction.v`.
- Do not add `PeriodicAnalysisMode` yet. The final checker still includes the
  conservative `edf_schedulability_decide` guard internally, so adding an
  `OffsetWindow` final-certificate mode would be misleading.
- Do not alter the CSV runner. It has no full `EDFInfiniteCert + sidecar` input
  format yet.

## Acceptance Checks

Rocq:

```sh
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicPolicyAnalysis.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicPolicyAnalysisEntryPoints.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtraction.vo
```

Extraction:

```sh
make -C scheduling_theory extract-periodic-edf-sched-hs
rg -n "PeriodicPolicy|check_periodic_policy_feasibility" scheduling_theory/extracted/haskell/PeriodicEDFSchedulability.hs
```

Regression:

```sh
make -C scheduling_theory test-periodic-edf-sched-csv
git -C scheduling_theory diff --check
```

## Out of Scope

- Full final-certificate CLI input format.
- LLF-specific certificate generation.
- Automatic discharge of the EDF busy-prefix bridge premise for LLF.
- Runtime hooks, traces, dispatch, timers, migration, and OS events.

## Known Dirty Files to Avoid

`scripts/test.csv` is an existing untracked file and is not part of Stage 4.
