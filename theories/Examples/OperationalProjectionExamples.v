From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
Import ListNotations.

Section OperationalProjectionExamples.

  Definition op_example_job : Job := mkJob 0 0 0 1 2.
  Definition op_example_jobs (_ : JobId) : Job := op_example_job.

  Definition one_cpu_trace (t : Time) : OpState :=
    match t with
    | 0 => mkOpState (fun _ => None) [0] (fun _ => true)
    | 1 => mkOpState (fun c => if Nat.eqb c 0 then Some 0 else None) [] (fun _ => false)
    | _ => mkOpState (fun _ => None) [] (fun _ => false)
    end.

  Example one_cpu_projection_reads_current_slot :
    project_schedule one_cpu_trace 1 0 = Some 0.
  Proof.
    reflexivity.
  Qed.

  Example one_cpu_current_implies_running :
    projected_running 1 one_cpu_trace 0 1.
  Proof.
    apply current_implies_projected_running with (c := 0).
    - lia.
    - reflexivity.
  Qed.

  Definition two_cpu_trace (_ : Time) : OpState :=
    mkOpState
      (fun c =>
         if Nat.eqb c 0 then Some 0
         else if Nat.eqb c 1 then Some 1
              else None)
      []
      (fun _ => false).

  Lemma two_cpu_trace_no_dup_state :
    forall t, op_no_duplication 2 (two_cpu_trace t).
  Proof.
    intros t j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
    assert (Hc1 : c1 = 0 \/ c1 = 1) by lia.
    assert (Hc2 : c2 = 0 \/ c2 = 1) by lia.
    destruct Hc1 as [-> | ->]; destruct Hc2 as [-> | ->];
      simpl in *.
    - reflexivity.
    - inversion Hrun1. inversion Hrun2. subst. discriminate.
    - inversion Hrun1. inversion Hrun2. subst. discriminate.
    - reflexivity.
  Qed.

  Example two_cpu_projection_has_no_duplication :
    no_duplication 2 (project_schedule two_cpu_trace).
  Proof.
    apply op_no_duplication_implies_projected_no_duplication.
    exact two_cpu_trace_no_dup_state.
  Qed.

  Lemma one_cpu_trace_projectable :
    projectable_trace op_example_jobs 1 one_cpu_trace.
  Proof.
    refine (mkProjectableTrace op_example_jobs 1 one_cpu_trace _ _ _).
    - intros t j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
      lia.
    - intros t c j Hlt Hrun.
      destruct t as [|[|t']]; simpl in Hrun; try discriminate.
      inversion Hrun; subst.
      unfold released, op_example_jobs, op_example_job.
      simpl.
      lia.
    - intros t c j Hlt Hrun.
      destruct t as [|[|t']]; simpl in Hrun; try discriminate.
      inversion Hrun; subst.
      unfold completed, service_job, cpu_count, runs_on, op_example_jobs, op_example_job.
      simpl.
      lia.
  Qed.

  Example projected_schedule_is_valid :
    valid_schedule op_example_jobs 1 (project_schedule one_cpu_trace).
  Proof.
    apply projectable_trace_implies_valid_schedule.
    exact one_cpu_trace_projectable.
  Qed.

  Example projected_schedule_service_is_available :
    service_job 1 (project_schedule one_cpu_trace) 0 2 = 1.
  Proof.
    reflexivity.
  Qed.

End OperationalProjectionExamples.
