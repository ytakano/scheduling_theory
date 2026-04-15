From RocqSched Require Import Multicore.Partitioned.PartitionedEntryPoints.
From RocqSched Require Import Examples.SchedulableExamples.
From RocqSched Require Import Examples.PeriodicExamples.
From RocqSched Require Import Examples.SporadicExamples.
From RocqSched Require Import Examples.JitteredPeriodicExamples.

(** * Curated examples for the partitioned theorem layer

    This file collects representative downstream entry points in one place.
    It intentionally re-exports existing example results instead of duplicating
    their proofs. *)

Definition partitioned_example_local_witness_to_edf :=
  pair_partitioned_edf_schedulable_by_on.

Definition partitioned_example_local_schedulable_to_edf :=
  pair_partitioned_edf_schedulable_by_on_via_local_schedulable.

Definition partitioned_example_local_feasible_to_edf :=
  pair_partitioned_edf_schedulable_by_on_via_local_feasible.

Definition partitioned_example_local_feasible_to_llf :=
  pair_partitioned_llf_schedulable_by_on_via_local_feasible.

Definition partitioned_example_periodic_to_edf :=
  periodic_example_partitioned_edf_schedulable_by_on.

Definition partitioned_example_sporadic_to_edf :=
  sporadic_example_partitioned_edf_schedulable_by_on.

Definition partitioned_example_jittered_periodic_to_edf :=
  jittered_periodic_example_partitioned_edf_schedulable_by_on.
