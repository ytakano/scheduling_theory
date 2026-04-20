From RocqSched Require Export Operational.Common.State.
From RocqSched Require Export Operational.Common.Trace.
From RocqSched Require Export Operational.Common.Step.
From RocqSched Require Export Operational.Common.Invariants.
From RocqSched Require Export Operational.Common.StepLemmas.
From RocqSched Require Export Operational.Common.Execution.
From RocqSched Require Export Operational.Common.LabeledExecution.
From RocqSched Require Export Operational.Common.DelayModel.
From RocqSched Require Export Operational.Common.DelayBudget.
From RocqSched Require Export Operational.Common.Projection.
From RocqSched Require Export Operational.Common.ProjectionLemmas.
From RocqSched Require Export Operational.Common.ProjectionInvariants.
From RocqSched Require Export Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Export Operational.Common.OSProjectionInterface.
From RocqSched Require Export Operational.Common.ConcreteExecution.
From RocqSched Require Export Operational.Common.OSLocalAdapterContract.
From RocqSched Require Export Operational.Common.OSAdapterContract.
From RocqSched Require Export Operational.Common.OSCausalityContract.
From RocqSched Require Export Operational.Common.OSSchedulerViewContract.
From RocqSched Require Export Operational.Common.OSHandoffContract.
From RocqSched Require Export Operational.Common.OSCandidateSourceContract.
From RocqSched Require Export Operational.Common.OSAdmissibleCandidateSourceContract.
From RocqSched Require Export Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Export Operational.Common.OSAlgorithmAdapterContract.
From RocqSched Require Export Refinement.OSCausalityTheorem.
From RocqSched Require Export Refinement.OSSchedulerViewTheorem.
From RocqSched Require Export Refinement.OSHandoffTheorem.
From RocqSched Require Export Refinement.OSCandidateSourceTheorem.
From RocqSched Require Export Refinement.OSAdmissibleCandidateSourceTheorem.
From RocqSched Require Export Refinement.OSSchedulerRelationTheorem.
From RocqSched Require Export Refinement.OSAlgorithmAdapterTheorem.
From RocqSched Require Export Refinement.OSRefinementTheorem.

(** * Stable public entry point for OS-neutral operational projection

    This file is the canonical downstream import for the reusable
    OS-neutral operational projection layer.

    Public theorem families exposed here:
    - proof-relevant operational scheduler state
    - operational traces
    - small-step operational skeleton
    - structural invariants
    - execution packaging
    - event-labeled execution packaging
    - delay-source classification and cumulative delay budgets
    - OS-neutral projection from concrete traces to operational traces
    - projection from operational traces to semantic schedules
    - local adapter-facing projection contracts
    - canonical adapter-facing contract records
    - scheduling-causality contracts over projected executions
    - scheduler-visible job contracts over projected executions
    - scheduler-handoff contracts over projected executions
    - candidate-source contracts over projected executions
    - admissibility-aware candidate-source contracts over projected executions
    - scheduler-relation contracts from projected executions to generic algorithms
    - schedule-parametric algorithm adapter contracts
    - projection soundness lemmas
    - multicore validity and placement bridge lemmas
    - OS-neutral refinement wrappers from adapter contracts

    Not part of this layer:
    - concrete OS-specific state definitions
    - concrete kernel adapters
    - policy-specific scheduler implementations
    - full interrupt / timer / IPI semantics
    - scheduling-point witness paths
    - schedulability analysis *)
