From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
Import ListNotations.

Section OperationalProjectionExamples.

  Definition op_example_job : Job := mkJob 0 0 0 1 2.
  Definition op_example_jobs (_ : JobId) : Job := op_example_job.

  Definition op_example_long_job : Job := mkJob 0 0 0 3 10.
  Definition op_example_long_jobs (_ : JobId) : Job := op_example_long_job.

  Definition one_cpu_state0 : OpState :=
    mkOpState (fun _ => None) [0] (fun _ => true).

  Definition one_cpu_state1 : OpState :=
    clear_need_resched 0
      (mkOpState
         (fun c => if Nat.eqb c 0 then Some 0 else op_current one_cpu_state0 c)
         (remove_job 0 (op_runnable one_cpu_state0))
         (op_need_resched one_cpu_state0)).

  Definition one_cpu_state2 : OpState :=
    clear_current_and_request 0 one_cpu_state1.

  Definition one_cpu_trace (t : Time) : OpState :=
    match t with
    | 0 => one_cpu_state0
    | 1 => one_cpu_state1
    | _ => one_cpu_state2
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

  Lemma one_cpu_trace_stepwise :
    trace_stepwise one_cpu_trace.
  Proof.
    intros [|[|t]].
    - exists (EvDispatch 0 0).
      constructor.
      + simpl. left. reflexivity.
      + reflexivity.
    - exists (EvComplete 0).
      constructor.
    - exists EvTick.
      constructor.
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

  Lemma one_cpu_state_struct_inv :
    forall t, op_struct_inv 1 (one_cpu_trace t).
  Proof.
    intros [|[|t']].
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        lia.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hlt Hcur Hin.
        simpl in Hcur. discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        assert (c1 = 0) by lia.
        assert (c2 = 0) by lia.
        subst c1 c2. reflexivity.
      + constructor.
      + intros c j Hlt Hcur Hin.
        assert (c = 0) by lia.
        subst c.
        simpl in Hcur.
        inversion Hcur; subst.
        simpl in Hin.
        contradiction.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        lia.
      + constructor.
      + intros c j Hlt Hcur Hin.
        assert (c = 0) by lia.
        subst c.
        unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hcur.
        simpl in Hcur.
        discriminate.
  Qed.

  Definition one_cpu_execution : execution 1 :=
    mkExecution 1 one_cpu_trace True one_cpu_trace_stepwise one_cpu_state_struct_inv.

  Lemma one_cpu_execution_sound :
    execution_projection_sound op_example_long_jobs 1 one_cpu_execution.
  Proof.
    constructor.
    - intros t c j Hlt Hrun.
      destruct t as [|t'].
      + simpl in Hrun. discriminate.
      + destruct t' as [|t''].
        * assert (c = 0) by lia.
          subst c.
          inversion Hrun; subst.
          unfold released, op_example_long_jobs, op_example_long_job.
          simpl.
          lia.
        * assert (c = 0) by lia.
          subst c.
          unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hrun.
          simpl in Hrun.
          discriminate.
    - intros t c j Hlt Hrun.
      destruct t as [|t'].
      + simpl in Hrun. discriminate.
      + destruct t' as [|t''].
        * assert (c = 0) by lia.
          subst c.
          inversion Hrun; subst.
          unfold completed, service_job, cpu_count, runs_on, project_schedule,
                 op_example_long_jobs, op_example_long_job.
          simpl.
          lia.
        * assert (c = 0) by lia.
          subst c.
          unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hrun.
          simpl in Hrun.
          discriminate.
  Qed.

  Example execution_projection_sound_yields_valid_schedule :
    valid_schedule op_example_long_jobs 1 (project_schedule (ex_trace one_cpu_execution)).
  Proof.
    apply execution_projection_sound_implies_valid_schedule.
    exact one_cpu_execution_sound.
  Qed.

  Lemma one_cpu_execution_projectable :
    projectable_trace op_example_long_jobs 1 (ex_trace one_cpu_execution).
  Proof.
    apply execution_projection_sound_implies_projectable.
    exact one_cpu_execution_sound.
  Qed.

  Example projected_schedule_is_valid :
    valid_schedule op_example_long_jobs 1 (project_schedule one_cpu_trace).
  Proof.
    apply projectable_trace_implies_valid_schedule.
    exact one_cpu_execution_projectable.
  Qed.

  Example projected_schedule_service_is_available :
    service_job 1 (project_schedule one_cpu_trace) 0 2 = 1.
  Proof.
    reflexivity.
  Qed.

End OperationalProjectionExamples.
