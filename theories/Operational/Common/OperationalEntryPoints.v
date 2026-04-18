From RocqSched Require Export Operational.Common.State.
From RocqSched Require Export Operational.Common.Trace.
From RocqSched Require Export Operational.Common.Step.
From RocqSched Require Export Operational.Common.Invariants.
From RocqSched Require Export Operational.Common.StepLemmas.
From RocqSched Require Export Operational.Common.Execution.
From RocqSched Require Export Operational.Common.Projection.
From RocqSched Require Export Operational.Common.ProjectionLemmas.
From RocqSched Require Export Operational.Common.OSProjectionInterface.
From RocqSched Require Export Operational.Common.ConcreteExecution.

(** * Stable public entry point for OS-neutral operational projection

    This file is the canonical downstream import for the reusable
    OS-neutral operational projection layer.

    Public theorem families exposed here:
    - proof-relevant operational scheduler state
    - operational traces
    - small-step operational skeleton
    - structural invariants
    - execution packaging
    - OS-neutral projection from concrete traces to operational traces
    - projection from operational traces to semantic schedules
    - projection soundness lemmas

    Not part of this layer:
    - concrete OS-specific state definitions
    - concrete kernel adapters
    - policy-specific scheduler implementations
    - full interrupt / timer / IPI semantics
    - schedulability analysis *)
