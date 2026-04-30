# Stage 2 N Kernel Extraction Boundary

## Goal

Stage 2 may introduce checker-local kernels indexed by Rocq `N`, the binary
natural number type. The goal is performance for finite enumeration, demand, or
cutoff computations without changing the common scheduling interface.

The common interface remains `nat`-based. `Time`, `CPU`, `TaskId`, `JobId`,
task costs, periods, deadlines, service, and remaining cost are still specified
by the existing common-layer definitions. The `N` kernel is an implementation
choice inside extracted checker code, not a new semantic domain.

## Interface Delta

The extraction configuration maps checker-local `N` values to Haskell
`Integer` alongside the existing `nat` to `Integer` mapping. This is an
extraction representation delta only. It does not add fields to common records,
new operational events, new trace rows, or new adapter-visible scheduler
policies.

Any Stage 2 entry point that exposes an `N`-indexed computation must keep a
`nat`-facing theorem or wrapper at the proof boundary. The abstract interface
seen by downstream proofs should state results over `nat`; conversions between
`nat` and `N` are proof obligations of the checker kernel or its adapter-facing
bridge.

## Observable Events Or Projection Points

No new common observable event is introduced by the `N` representation.
Existing projection points remain:

- checker input artifacts such as finite task descriptions and trace-derived
  tables;
- checker boolean results and diagnostics envelopes;
- adapter-local projection from emitted runtime artifacts to the finite
  objects consumed by the checker.

The Haskell `Integer` representation of `N` is not itself observable evidence.
External parsers and wrappers must continue to reject negative numbers before
passing values to extracted code that represents `N` as `Integer`.

## Common-Layer Proof Obligations

The common layer should remain minimal:

- define the abstract `nat` contracts for time, identifiers, service, demand,
  and schedule-facing predicates;
- provide any reusable conversion lemmas only when they are independent of a
  concrete checker algorithm;
- avoid depending on Haskell `Integer`, parser behavior, trace serialization,
  or checker diagnostics.

The common layer does not prove that a particular Stage 2 `N` kernel is fast,
complete for a concrete input format, or safe for negative external integers.

## Downstream Adapter Obligations

An adapter that uses a Stage 2 `N` kernel must discharge local, checkable
responsibilities:

- show that every external numeric input accepted by the adapter is
  nonnegative and corresponds to the intended `nat` value;
- relate each `N`-indexed kernel result back to the `nat` theorem consumed by
  the common or refinement layer;
- preserve the existing projection boundary from runtime artifacts to finite
  checker input objects;
- keep unsupported-policy, parse-error, overflow-policy, and diagnostics
  decisions adapter-local.

These obligations belong to the adapter or checker bridge, not to the common
semantic interface.

## Runtime Implementation Impact

There is no required concrete runtime change for this extraction support. Stage
2 should not add scheduler hooks, interrupt hooks, queue fields, or trace rows
only because the checker kernel uses `N`. Runtime changes are justified only
when a checker needs a new observable artifact, and that artifact must be
documented as adapter-local unless a separate common interface is introduced.

## Design-Document Impact

Design documents should describe `N` kernels as checker-local acceleration.
They should keep three layers separate:

- common layer: `nat` contracts and reusable theorem statements;
- adapter layer: parsing, projection, nonnegativity, and conversion
  obligations;
- concrete runtime layer: emitted artifacts and hooks, only when needed.

Avoid wording that treats Haskell `Integer` or Rocq `N` as the common notion of
time or identifiers.

## Test Planning

Stage 2 tests should be planned around the boundary, not around Haskell wrapper
rewrites:

- extraction smoke test: compile the shared extraction configuration and a
  small `N`-using extraction entry point;
- representation test: confirm generated Haskell uses `Prelude.Integer` for
  both `nat` and checker-local `N`;
- parser-boundary test: reject negative external values before they enter an
  extracted `N` kernel;
- conversion test: compare a small bounded `N` kernel result with the existing
  `nat` checker theorem or reference computation;
- regression test: existing periodic, jittered, and Awkernel extracted checker
  entry points still build and keep their current external CLI behavior.

Do not implement these tests by modifying periodic or jittered checker logic or
handwritten Haskell wrappers as part of the extraction-boundary change.

## Open Risks

Mapping `N` to Haskell `Integer` relies on adapter-side input discipline:
negative `Integer` values are outside the intended representation. If a future
wrapper bypasses the parser boundary, the extracted recursor can observe values
that do not correspond to Rocq `N`. Stage 2 must therefore keep nonnegativity
checks and conversion lemmas explicit.
