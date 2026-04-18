# Phase D: Multicore Semantic Boundary

Phase D closes the semantic boundary between:

- `Multicore/Common`
- `Multicore/Global`
- `Analysis/Multicore`

The target end state is:

- policy-independent multicore semantic facts live in `Multicore/Common`
- global EDF / LLF remain thin policy wrappers over the generic top-`m` layer
- analysis files consume common/global boundaries but are not imported back by them

## Completed in this phase

- machine-supply semantic theorems live in `Multicore/Common/ServiceFacts.v`
- `Analysis/Multicore/ProcessorSupply.v` is now an analysis-facing re-export wrapper
- `Multicore/Common/ValidityFacts.v` packages multicore semantic validity
- `Multicore/Common/TopMSelectionFacts.v` packages interval full-supply consequences
- `Multicore/Common/MulticoreSemanticsEntryPoints.v` exports the new common theorem layers
- global EDF / LLF expose thin semantic-validity wrappers and use common interval full-supply hooks
- workload-absorption clients use common interval/non-running facts and the bundled validity record

## Phase-D completion checks

- `Multicore/Common` and `Multicore/Global` do not import `Analysis/Multicore/*`
- common multicore clients can start from `MulticoreSemanticsEntryPoints.v`
- interval full-supply reasoning is reachable from the common top-`m` boundary
- global EDF / LLF add policy-specific scheduling and metric-order content on top of the shared layer

## Explicit non-goals

- new scheduling policies
- richer affinity examples
- operational/refinement integration
- stronger fairness statements beyond the current analysis clients
