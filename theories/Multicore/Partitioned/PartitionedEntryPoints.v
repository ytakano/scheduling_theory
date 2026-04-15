From RocqSched Require Export Multicore.Partitioned.Partitioned.
From RocqSched Require Export Multicore.Partitioned.PartitionedCompose.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedPolicyLift.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedFiniteOptimalityLift.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedEDF.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedFIFO.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedRR.
From RocqSched Require Export Multicore.Partitioned.Policies.PartitionedLLF.
From RocqSched Require Export TaskModels.Periodic.PeriodicPartitionedFiniteOptimalityLift.
From RocqSched Require Export TaskModels.Sporadic.SporadicPartitionedFiniteOptimalityLift.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicPartitionedFiniteOptimalityLift.

(** * Stable public entry points for the partitioned theorem layer

    This file is the canonical downstream import for the reusable partitioned
    multicore theorem layer.

    Public theorem families exposed here:
    - generic composition and service localization:
      [local_witnesses_imply_partitioned_schedulable_by_on],
      [local_schedulable_by_on_implies_partitioned_schedulable_by_on],
      [glue_feasible_on_if_local_feasible_on],
      [service_partitioned_eq_local_service]
    - generic wrapper and finite-optimality lifts
    - policy wrappers for EDF / FIFO / RR / LLF
    - task-model lifts for periodic / sporadic / jittered-periodic jobs

    Policy boundary:
    - EDF / LLF are finite-optimality-ready and expose local-feasible entry
      points through the generic partitioned finite-optimality lift.
    - FIFO / RR are intentionally wrapper-only for now; they expose witness-
      based and local-schedulable entry points, but no finite-optimality-based
      partitioned lift yet. *)
