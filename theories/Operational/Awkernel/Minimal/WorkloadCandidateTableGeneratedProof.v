From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateTable.
From RocqSched Require Import Operational.Awkernel.Minimal.Generated.WorkloadTraceArtifact.
From RocqSched Require Import Operational.Awkernel.Minimal.Generated.WorkloadCandidateTable.

Definition awk_generated_workload_rows := awk_generated_handoff_rows.

Definition awk_generated_workload_candidates : CandidateSource :=
  candidate_source_of_table awk_generated_candidate_table.

Example awk_generated_candidate_table_matches_rows :
  candidate_table_matches_rows
    awk_generated_workload_rows
    awk_generated_candidate_table = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example awk_generated_candidate_table_contract :
  workload_candidate_table_contract
    awk_generated_workload_rows
    awk_generated_candidate_table.
Proof.
  apply candidate_table_matches_rows_sound.
  exact awk_generated_candidate_table_matches_rows.
Qed.

Example awk_generated_workload_candidates_prefix_extensional :
  forall jobs m s1 s2 t,
    (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
    awk_generated_workload_candidates jobs m s1 t =
    awk_generated_workload_candidates jobs m s2 t.
Proof.
  intros jobs m s1 s2 t Hprefix.
  apply candidate_source_of_table_prefix_extensional.
  exact Hprefix.
Qed.
