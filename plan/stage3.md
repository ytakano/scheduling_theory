# Stage 3: offset-aware feasibility checker surface

Stage 3 removes the public zero-offset bias from the final certificate checker
surface. The existing checker implementation already has an offset-aware path,
`check_periodic_edf_checked_sidecar_extracted_with_offsets`, using
`extracted_periodic_offsets`, `extracted_offset_periodic_jobs`, and
`extracted_offset_periodic_codec`. Stage 3 promotes that path through
feasibility-facing aliases while preserving the older EDF/zero-offset names for
compatibility.

This stage is still proof/extraction/adapter work. It does not add runtime
scheduler hooks, QEMU behavior, trace semantics, timer behavior, migration
semantics, or OS-specific events.

## Goal

- Make the offset-aware final checker the primary public checker for extracted
  task sets.
- Keep zero-offset EDF-named definitions and theorems available as compatibility
  wrappers.
- Introduce feasibility-facing names needed by the later LLF connection.
- Avoid a bulk rewrite of historical `(fun _ => 0)` lemmas; only the public
  surface changes in this stage.

## Public Interface Delta

Add aliases in `PeriodicEDFFinalCertificateChecker.v`:

```coq
Definition PeriodicFeasibilityCheckedSidecarCert :=
  PeriodicEDFCheckedSidecarCert.

Definition check_periodic_feasibility_checked_sidecar_extracted
    (ts : list ExtractedPeriodicTask)
    (cert : EDFInfiniteCert JobId)
    (sidecar : PeriodicFeasibilityCheckedSidecarCert) : bool :=
  check_periodic_edf_checked_sidecar_extracted_with_offsets ts cert sidecar.
```

Add proof-facing wrappers:

- `check_periodic_feasibility_checked_sidecar_sound_with_hyperperiod_transport`
- `check_periodic_feasibility_checked_sidecar_sound_with_completion_transport_generated_rep`

Both wrappers delegate to the existing offset-aware EDF-generated witness
theorems. They prove schedulability of the extracted offset-aware periodic
jobset under EDF, not policy-neutral LLF schedulability.

Export the new aliases from `PeriodicEDFExtraction.v`:

- `PeriodicFeasibilityCheckedSidecarCert`
- `check_periodic_feasibility_checked_sidecar_extracted`

Do not remove `PeriodicEDFCheckedSidecarCert`,
`check_periodic_edf_checked_sidecar_extracted_with_offsets`, or
`check_periodic_edf_checked_sidecar_extracted`.

## Adapter Boundary

The CSV `--check-prefix-cert` mode remains a prefix-only smoke checker because
it constructs only an `EDFPrefixCert`, not a full `EDFInfiniteCert` plus
sidecar. It should continue checking prefix semantic validity and generated EDF
prefix matching with offset-aware jobs and codec.

A future final-certificate CLI should accept or generate the full
`EDFInfiniteCert` and `PeriodicFeasibilityCheckedSidecarCert` before calling
`check_periodic_feasibility_checked_sidecar_extracted`.

## Implementation Order

1. Add the feasibility certificate type alias and checker alias.
2. Add the two feasibility soundness wrappers.
3. Export the new names through extraction.
4. Keep the existing prefix-only CSV behavior unchanged.
5. Regenerate extracted Haskell.
6. Update this plan and `stage2.md`/future roadmap text only if they describe
   Stage 3 feasibility aliases as missing.

## Acceptance Checks

Rocq:

```sh
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFFinalCertificateChecker.vo
make -C scheduling_theory theories/TaskModels/Periodic/PeriodicEDFExtraction.vo
```

Extraction:

```sh
make -C scheduling_theory extract-periodic-edf-sched-hs
rg -n "PeriodicFeasibility|check_periodic_feasibility" scheduling_theory/extracted/haskell/PeriodicEDFSchedulability.hs
```

CLI regression:

```sh
make -C scheduling_theory test-periodic-edf-sched-csv
```

Repository hygiene:

```sh
git -C scheduling_theory diff --check
git -C scheduling_theory status --short --untracked-files=all
```

## Out of Scope

- Replacing every historical zero-offset theorem.
- Full final-certificate CLI input format.
- LLF policy-neutral schedulability theorem.
- Runtime hooks, traces, dispatch, timers, migration, and OS events.

## Known Dirty Files to Avoid

`scripts/test.csv` is an existing untracked file and is not part of Stage 3.
