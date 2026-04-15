From RocqSched Require Import Multicore.Global.GlobalEntryPoints.
From RocqSched Require Import Examples.GlobalInterferenceExamples.
From RocqSched Require Import Examples.GlobalServiceExamples.
From RocqSched Require Import Examples.GlobalLLFExamples.
From RocqSched Require Import Examples.GlobalWorkConservingExamples.

(** * Curated examples for the global theorem layer

    This file collects representative downstream entry points in one place.
    It intentionally re-exports existing example results instead of duplicating
    their proofs. *)

Definition global_example_running_from_admissible_somewhere :=
  global_edf_running_from_admissible_somewhere_example.

Definition global_example_llf_excluded_job_has_more_laxity :=
  global_llf_cpu0_has_le_laxity_than_excluded_job_example.

Definition global_example_llf_excluded_job_implies_machine_full :=
  global_llf_excluded_eligible_job_implies_machine_full_example.

Definition global_example_llf_excluded_job_interval_implies_full_supply :=
  global_llf_excluded_eligible_job_interval_implies_full_supply_example.

Definition global_example_covering_list_recovers_machine_supply :=
  global_covering_list_recovers_machine_supply_example.

Definition global_example_service_preserved_under_migration :=
  migrating_global_service_is_preserved.

Definition global_example_interval_service_preserved_under_migration :=
  migrating_interval_service_is_preserved.

Definition global_example_service_sum_matches_global_service :=
  migrating_service_matches_sum_of_cpu_services.

Definition global_example_machine_supply_bounded_by_capacity :=
  migrating_machine_supply_bounded_by_capacity.

Definition global_example_no_duplication_interval_service_bound :=
  migrating_no_duplication_interval_service_bound.

Definition global_example_laxity_preserved_while_running :=
  migrating_laxity_is_preserved_while_running.

Definition global_example_duplicate_schedule_rejected :=
  duplicate_schedule_not_no_duplication.

Definition global_example_duplicate_schedule_exceeds_unit_length :=
  duplicate_schedule_interval_service_exceeds_unit_length.
