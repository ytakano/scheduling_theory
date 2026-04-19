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
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
Import ListNotations.

Section OperationalProjectionExamples.

  Definition op_example_job : Job := mkJob 0 0 0 1 2.
  Definition op_example_jobs (_ : JobId) : Job := op_example_job.

  Definition op_example_long_job : Job := mkJob 0 0 0 3 10.
  Definition op_example_long_jobs (_ : JobId) : Job := op_example_long_job.

  Definition one_cpu_state0 : OpState :=
    mkOpState (fun _ => None) [0] (fun _ => true) (fun c => if Nat.eqb c 0 then Some 0 else None).

  Definition one_cpu_state1 : OpState :=
    dispatch_on_cpu 0 0 one_cpu_state0.

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
      + simpl. reflexivity.
      + reflexivity.
    - exists (EvComplete 0).
      constructor.
      exists 0. reflexivity.
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
      (fun _ => false)
      (fun _ => None).

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
        simpl in Hrun1.
        discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur. discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        assert (c1 = 0) by lia.
        subst c1.
        simpl in Ht1.
        inversion Ht1; subst.
        lia.
      + intros c j Hlt Ht.
        assert (c = 0) by lia.
        subst c.
        simpl in Ht.
        inversion Ht; subst.
        simpl. left. reflexivity.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        assert (c1 = 0) by lia.
        assert (c2 = 0) by lia.
        subst c1 c2. reflexivity.
      + constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        destruct (Nat.eqb c 0) eqn:Ec; try discriminate.
        inversion Hcur; subst.
        simpl in Hin.
        contradiction.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        unfold one_cpu_state1, one_cpu_state0 in Ht1.
        simpl in Ht1.
        exfalso.
        destruct (Nat.eqb c1 0); discriminate.
      + intros c j Hlt Ht.
        unfold one_cpu_state1, one_cpu_state0 in Ht.
        simpl in Ht.
        destruct (Nat.eqb c 0); discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        lia.
      + constructor.
      + intros c j Hcur Hin.
        unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hcur.
        simpl in Hcur.
        destruct (Nat.eqb c 0); discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Ht1.
        simpl in Ht1.
        destruct (Nat.eqb c1 0); discriminate.
      + intros c j Hlt Ht.
        unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Ht.
        simpl in Ht.
        destruct (Nat.eqb c 0); discriminate.
  Qed.

  Definition one_cpu_execution : execution 1 :=
    mkExecution 1 one_cpu_trace True one_cpu_trace_stepwise one_cpu_state_struct_inv.

  Definition preempt_state0 : OpState :=
    mkOpState
      (fun c => if Nat.eqb c 0 then Some 0 else None)
      [1]
      (fun c => if Nat.eqb c 0 then true else false)
      (fun c => if Nat.eqb c 0 then Some 1 else None).

  Definition preempt_state1 : OpState :=
    preempt_on_cpu 0 0 1 preempt_state0.

  Example preempt_state_switches_running_job :
    op_current preempt_state1 0 = Some 1.
  Proof.
    reflexivity.
  Qed.

  Example preempt_state_requeues_old_job :
    op_runnable preempt_state1 = [0].
  Proof.
    reflexivity.
  Qed.

  Example preempt_step_is_available :
    op_step preempt_state0 (EvPreempt 0 0 1) preempt_state1.
  Proof.
    constructor.
    - reflexivity.
    - intros c' Hcur.
      destruct (Nat.eqb c' 0) eqn:Ec'; [apply Nat.eqb_eq in Ec'; exact Ec'|].
      simpl in Hcur.
      rewrite Ec' in Hcur.
      discriminate.
    - reflexivity.
    - discriminate.
  Qed.

  Definition example_concrete_state : Type := nat.

  Definition example_projection_state (n : nat) : OpState :=
    match n with
    | 0 => one_cpu_state0
    | 1 => one_cpu_state1
    | _ => one_cpu_state2
    end.

  Definition example_projection : OSLabeledProjection example_concrete_state :=
    mkOSLabeledProjection
      example_concrete_state
      (mkOSProjection example_concrete_state example_projection_state)
      (fun s s' =>
         match s, s' with
         | 0, 1 => EvDispatch 0 0
         | 1, _ => EvComplete 0
         | _, _ => EvTick
         end).

  Definition example_concrete_trace : concrete_trace example_concrete_state :=
    fun t =>
      match t with
      | 0 => 0
      | 1 => 1
      | _ => 2
      end.

  Lemma example_concrete_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection example_projection) (example_concrete_trace t))
        (os_step_label example_projection
           (example_concrete_trace t)
           (example_concrete_trace (S t)))
        (os_to_op_state
           (osl_to_os_projection example_projection)
           (example_concrete_trace (S t))).
  Proof.
    intros [|[|t]]; simpl.
    - constructor.
      + reflexivity.
      + reflexivity.
    - constructor.
      exists 0. reflexivity.
    - constructor.
  Qed.

  Lemma example_concrete_struct_inv :
    forall t,
      op_struct_inv
        1
        (os_to_op_state
           (osl_to_os_projection example_projection)
           (example_concrete_trace t)).
  Proof.
    intros [|[|t]]; simpl.
    - change (op_struct_inv 1 (one_cpu_trace 0)).
      apply one_cpu_state_struct_inv.
    - change (op_struct_inv 1 (one_cpu_trace 1)).
      apply one_cpu_state_struct_inv.
    - change (op_struct_inv 1 (one_cpu_trace (S (S t)))).
      apply one_cpu_state_struct_inv.
  Qed.

  Definition example_labeled_concrete_execution :
      @labeled_concrete_execution example_concrete_state example_projection 1 :=
    @mkLabeledConcreteExecution
      example_concrete_state
      example_projection
      1
      example_concrete_trace
      True
      example_concrete_stepwise
      example_concrete_struct_inv.

  Example concrete_projection_exposes_dispatch_label :
    lex_event (concrete_to_labeled_execution example_labeled_concrete_execution) 0 =
    EvDispatch 0 0.
  Proof.
    reflexivity.
  Qed.

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
