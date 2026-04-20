From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Common.MetricChooser.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.TopMMetricChooser.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Trace.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.StepLemmas.
From RocqSched Require Import Operational.Common.Execution.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSAdapterContract.
From RocqSched Require Import Operational.Common.OSCausalityContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Operational.Common.OSHandoffContract.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSAdmissibleCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Refinement.OSCausalityTheorem.
From RocqSched Require Import Refinement.OSSchedulerViewTheorem.
From RocqSched Require Import Refinement.OSHandoffTheorem.
From RocqSched Require Import Refinement.OSCandidateSourceTheorem.
From RocqSched Require Import Refinement.OSAdmissibleCandidateSourceTheorem.
From RocqSched Require Import Refinement.OSSchedulerRelationTheorem.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Refinement.OSRefinementTheorem.
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
    - exists (EvBlock 0).
      constructor.
      exists 0. reflexivity.
    - exists EvStutter.
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
         | 1, _ => EvBlock 0
         | _, _ => EvStutter
         end).

  Definition example_concrete_trace : concrete_trace example_concrete_state :=
    fun t =>
      match t with
      | 0 => 0
      | 1 => 1
      | _ => 2
      end.

  Definition choose_state0 : OpState :=
    mkOpState (fun _ => None) [0] (fun _ => false) (fun _ => None).

  Definition choose_state1 : OpState :=
    set_dispatch_target 0 (Some 0) choose_state0.

  Definition choose_trace (t : Time) : OpState :=
    match t with
    | 0 => choose_state0
    | _ => choose_state1
    end.

  Definition choose_projection : OSLabeledProjection nat :=
    mkOSLabeledProjection
      nat
      (mkOSProjection nat (fun n => if Nat.eqb n 0 then choose_state0 else choose_state1))
      (fun s s' =>
         match s, s' with
         | 0, 1 => EvChoose 0 0
         | _, _ => EvStutter
         end).

  Definition choose_concrete_trace : concrete_trace nat :=
    fun t => if Nat.eqb t 0 then 0 else 1.

  Lemma choose_concrete_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection choose_projection) (choose_concrete_trace t))
        (os_step_label choose_projection
           (choose_concrete_trace t)
           (choose_concrete_trace (S t)))
        (os_to_op_state
           (osl_to_os_projection choose_projection)
           (choose_concrete_trace (S t))).
  Proof.
    intros [|t']; simpl.
    - constructor.
      + simpl. left. reflexivity.
      + reflexivity.
      + intros [c' Hpending].
        simpl in Hpending.
        destruct c'; discriminate.
    - constructor.
  Qed.

  Lemma choose_concrete_struct_inv :
    forall t,
      op_struct_inv
        1
        (os_to_op_state (osl_to_os_projection choose_projection) (choose_concrete_trace t)).
  Proof.
    intros [|t']; simpl.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        simpl in Hrun1.
        discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        assert (c1 = 0) by lia.
        subst c1.
        simpl in Ht1.
        discriminate.
      + intros c j Hlt Ht.
        simpl in Ht.
        discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        simpl in Hrun1.
        discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        discriminate.
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
  Qed.

  Definition choose_labeled_concrete_execution :
      @labeled_concrete_execution nat choose_projection 1 :=
    @mkLabeledConcreteExecution
      nat
      choose_projection
      1
      choose_concrete_trace
      True
      choose_concrete_stepwise
      choose_concrete_struct_inv.

  Definition wakeup_state0 : OpState :=
    mkOpState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition wakeup_state1 : OpState :=
    add_runnable 0 wakeup_state0.

  Definition wakeup_projection : OSLabeledProjection nat :=
    mkOSLabeledProjection
      nat
      (mkOSProjection nat (fun n => if Nat.eqb n 0 then wakeup_state0 else wakeup_state1))
      (fun s s' =>
         match s, s' with
         | 0, 1 => EvWakeup 0
         | _, _ => EvStutter
         end).

  Definition wakeup_concrete_trace : concrete_trace nat :=
    fun t => if Nat.eqb t 0 then 0 else 1.

  Lemma wakeup_concrete_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection wakeup_projection) (wakeup_concrete_trace t))
        (os_step_label wakeup_projection
           (wakeup_concrete_trace t)
           (wakeup_concrete_trace (S t)))
        (os_to_op_state
           (osl_to_os_projection wakeup_projection)
           (wakeup_concrete_trace (S t))).
  Proof.
    intros [|t']; simpl.
    - constructor.
    - constructor.
  Qed.

  Lemma wakeup_concrete_struct_inv :
    forall t,
      op_struct_inv
        1
        (os_to_op_state (osl_to_os_projection wakeup_projection) (wakeup_concrete_trace t)).
  Proof.
    intros [|t']; simpl.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        simpl in Hrun1.
        discriminate.
      + constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        simpl in Ht1.
        discriminate.
      + intros c j Hlt Ht.
        simpl in Ht.
        discriminate.
    - constructor.
      + intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
        simpl in Hrun1.
        discriminate.
      + constructor.
        * simpl. tauto.
        * constructor.
      + intros c j Hcur Hin.
        simpl in Hcur.
        discriminate.
      + intros j c1 c2 Hlt1 Hlt2 Ht1 _.
        simpl in Ht1.
        discriminate.
      + intros c j Hlt Ht.
        simpl in Ht.
        discriminate.
  Qed.

  Definition wakeup_labeled_concrete_execution :
      @labeled_concrete_execution nat wakeup_projection 1 :=
    @mkLabeledConcreteExecution
      nat
      wakeup_projection
      1
      wakeup_concrete_trace
      True
      wakeup_concrete_stepwise
      wakeup_concrete_struct_inv.

  Definition complete_projection : OSLabeledProjection nat :=
    mkOSLabeledProjection
      nat
      (mkOSProjection nat example_projection_state)
      (fun s s' =>
         match s, s' with
         | 0, 1 => EvDispatch 0 0
         | 1, _ => EvComplete 0
         | _, _ => EvStutter
         end).

  Lemma complete_concrete_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection complete_projection) (example_concrete_trace t))
        (os_step_label complete_projection
           (example_concrete_trace t)
           (example_concrete_trace (S t)))
        (os_to_op_state
           (osl_to_os_projection complete_projection)
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

  Lemma complete_concrete_struct_inv :
    forall t,
      op_struct_inv
        1
        (os_to_op_state
           (osl_to_os_projection complete_projection)
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

  Definition complete_labeled_concrete_execution :
      @labeled_concrete_execution example_concrete_state complete_projection 1 :=
    @mkLabeledConcreteExecution
      example_concrete_state
      complete_projection
      1
      example_concrete_trace
      True
      complete_concrete_stepwise
      complete_concrete_struct_inv.

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

  Lemma example_labeled_concrete_sound :
    labeled_concrete_projection_sound
      op_example_long_jobs
      1
      example_labeled_concrete_execution.
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

  Lemma example_local_labeled_concrete_sound :
    local_labeled_concrete_projection_sound
      op_example_long_jobs
      1
      example_labeled_concrete_execution.
  Proof.
    constructor.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
      unfold released, op_example_long_jobs, op_example_long_job.
      simpl.
      lia.
      + contradiction.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
        apply not_completed_iff_service_lt_cost.
        unfold service_job, cpu_count, runs_on, project_schedule,
               op_example_long_jobs, op_example_long_job.
        simpl.
        lia.
      + contradiction.
    - intros [|[|t']] c j Hlt Hrun; simpl in *.
      + assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        right. left. reflexivity.
      + destruct (Nat.eqb c 0); discriminate.
      + left. exact Hrun.
    - intros t c j Hlt Hdispatch.
      destruct t as [|t'].
      + inversion Hdispatch; subst.
        unfold released, op_example_long_jobs, op_example_long_job.
        simpl.
        lia.
      + destruct t' as [|t''].
        * simpl in Hdispatch.
          discriminate.
        * simpl in Hdispatch.
          discriminate.
    - intros t j Hwakeup.
      destruct t as [|[|t'']]; simpl in Hwakeup; inversion Hwakeup.
    - intros t j Hwakeup.
      destruct t as [|[|t'']]; simpl in Hwakeup; inversion Hwakeup.
    - intros t c j Hlt Hprev Hnext.
      assert (c = 0) by lia.
      subst c.
      destruct t as [|t'].
      + simpl in Hnext.
        discriminate.
      + destruct t' as [|t''].
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hprev, Hnext.
          simpl in Hprev, Hnext.
          discriminate.
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hprev, Hnext.
          simpl in Hprev, Hnext.
          discriminate.
    - intros t c Hlt Hreq.
      destruct t as [|t'].
      + simpl in Hreq.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hreq.
          discriminate.
        * simpl in Hreq.
          discriminate.
    - intros t c Hlt Hhandle.
      destruct t as [|t'].
      + simpl in Hhandle.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hhandle.
          discriminate.
        * simpl in Hhandle.
          discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t'].
      + simpl in Hchoose.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hchoose.
          discriminate.
        * simpl in Hchoose.
          discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t'].
      + simpl in Hchoose.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hchoose.
          discriminate.
        * simpl in Hchoose.
          discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t as [|t'].
      + inversion Hdispatch; subst.
        unfold completed, service_job, cpu_count, runs_on, project_schedule,
               op_example_long_jobs, op_example_long_job.
        simpl.
        lia.
      + destruct t' as [|t''].
        * simpl in Hdispatch.
          discriminate.
        * simpl in Hdispatch.
          discriminate.
    - intros t c j Hblock Hcur.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hcur.
          simpl in Hcur.
          destruct (Nat.eqb c 0); discriminate.
        * simpl in Hblock.
          discriminate.
    - intros t j Hblock.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0.
          simpl.
          exact (remove_job_not_in 0 [0]).
        * simpl in Hblock.
          discriminate.
    - intros t c j Hlt Hblock Htarget.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Htarget.
          simpl in Htarget.
          destruct (Nat.eqb c 0); discriminate.
        * simpl in Hblock.
          discriminate.
    - intros t j Hcomplete.
      destruct t as [|[|t'']]; simpl in Hcomplete; inversion Hcomplete.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
  Qed.

  Lemma example_labeled_concrete_multicore_sound :
    labeled_concrete_multicore_projection_sound
      op_example_long_jobs
      all_cpus_admissible
      1
      example_labeled_concrete_execution.
  Proof.
    constructor.
    - exact example_labeled_concrete_sound.
    - intros [|[|t']] c Hge; simpl.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
    - intros [|[|t']] c j Hlt Hrun.
      + simpl in Hrun.
        discriminate.
      + simpl in Hrun.
        assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        unfold all_cpus_admissible.
        exact I.
      + simpl in Hrun.
        destruct (Nat.eqb c 0); discriminate.
  Qed.

  Lemma example_local_labeled_concrete_multicore_sound :
    local_labeled_concrete_multicore_projection_sound
      op_example_long_jobs
      all_cpus_admissible
      1
      example_labeled_concrete_execution.
  Proof.
    constructor.
    - exact example_local_labeled_concrete_sound.
    - intros [|[|t']] c Hge; simpl.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
    - intros [|[|t']] c j Hlt Hrun.
      + simpl in Hrun.
        discriminate.
      + simpl in Hrun.
        assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        unfold all_cpus_admissible.
        exact I.
      + simpl in Hrun.
        destruct (Nat.eqb c 0); discriminate.
  Qed.

  Definition example_local_adapter_contract :
    os_local_multicore_adapter_contract
      example_projection
      op_example_long_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalMulticoreAdapterContract
      example_concrete_state
      example_projection
      op_example_long_jobs
      all_cpus_admissible
      1
      example_labeled_concrete_execution
      example_local_labeled_concrete_multicore_sound.

  Definition example_adapter_contract :
    os_multicore_adapter_contract
      example_projection
      op_example_long_jobs
      all_cpus_admissible
      1 :=
    @mkOSMulticoreAdapterContract
      example_concrete_state
      example_projection
      op_example_long_jobs
      all_cpus_admissible
      1
      example_labeled_concrete_execution
      example_labeled_concrete_multicore_sound.

  Example adapter_contract_yields_valid_schedule :
    valid_schedule
      op_example_long_jobs
      1
      (project_schedule
         (lex_trace
            (concrete_to_labeled_execution
               (oac_execution example_adapter_contract)))).
  Proof.
    apply os_multicore_adapter_contract_implies_valid_schedule.
  Qed.

  Example local_adapter_contract_yields_valid_schedule :
    valid_schedule
      op_example_long_jobs
      1
      (project_schedule
         (lex_trace
            (concrete_to_labeled_execution
               (olac_execution example_local_adapter_contract)))).
  Proof.
    apply os_local_multicore_adapter_contract_implies_valid_schedule.
  Qed.

  Lemma choose_local_labeled_concrete_sound :
    local_labeled_concrete_projection_sound
      op_example_jobs
      1
      choose_labeled_concrete_execution.
  Proof.
    constructor.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
      unfold released, op_example_jobs, op_example_job.
      simpl.
      lia.
      + contradiction.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
        apply not_completed_iff_service_lt_cost.
        unfold service_job, cpu_count, runs_on, project_schedule,
               op_example_jobs, op_example_job.
        simpl.
        lia.
      + contradiction.
    - intros [|t'] c j Hlt Hrun; simpl in *.
      + discriminate.
      + discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t; simpl in Hdispatch; discriminate.
    - intros t j Hwakeup.
      destruct t as [|t']; simpl in Hwakeup.
      + inversion Hwakeup.
      + discriminate.
    - intros t j Hwakeup.
      destruct t as [|t']; simpl in Hwakeup.
      + inversion Hwakeup.
      + discriminate.
    - intros t c j Hlt Hprev Hnext.
      destruct t; simpl in Hprev, Hnext; discriminate.
    - intros t c Hlt Hreq.
      destruct t; simpl in Hreq; discriminate.
    - intros t c Hlt Hhandle.
      destruct t; simpl in Hhandle; discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t']; simpl in Hchoose.
      + inversion Hchoose; subst.
        reflexivity.
      + discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t']; simpl in Hchoose.
      + inversion Hchoose; subst.
        simpl. left. reflexivity.
      + discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t; simpl in Hdispatch; discriminate.
    - intros t c j Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t j Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t c j Hlt Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t j Hcomplete.
      destruct t as [|[|t'']]; simpl in Hcomplete; inversion Hcomplete.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
  Qed.

  Example choose_local_contract_sets_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection choose_projection)
         (lce_trace choose_labeled_concrete_execution 1))
      0 = Some 0.
  Proof.
    eapply local_labeled_concrete_projection_sound_choose_sets_dispatch_target
      with (jobs := op_example_jobs) (ex := choose_labeled_concrete_execution) (t := 0)
           (c := 0) (j := 0).
    - exact choose_local_labeled_concrete_sound.
    - lia.
    - reflexivity.
  Qed.

  Example choose_local_contract_uses_runnable_job :
    In 0
       (op_runnable
          (os_to_op_state
             (osl_to_os_projection choose_projection)
             (lce_trace choose_labeled_concrete_execution 0))).
  Proof.
    eapply local_labeled_concrete_projection_sound_choose_from_runnable
      with (jobs := op_example_jobs) (ex := choose_labeled_concrete_execution) (t := 0)
           (c := 0) (j := 0).
    - exact choose_local_labeled_concrete_sound.
    - lia.
    - reflexivity.
  Qed.

  Lemma choose_local_labeled_concrete_multicore_sound :
    local_labeled_concrete_multicore_projection_sound
      op_example_jobs
      all_cpus_admissible
      1
      choose_labeled_concrete_execution.
  Proof.
    constructor.
    - exact choose_local_labeled_concrete_sound.
    - intros [|t'] c Hge; simpl.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
    - intros [|t'] c j Hlt Hrun.
      + simpl in Hrun. discriminate.
      + simpl in Hrun. discriminate.
  Qed.

  Definition choose_local_adapter_contract :
    os_local_multicore_adapter_contract
      choose_projection
      op_example_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalMulticoreAdapterContract
      nat
      choose_projection
      op_example_jobs
      all_cpus_admissible
      1
      choose_labeled_concrete_execution
      choose_local_labeled_concrete_multicore_sound.

  Definition choose_example_candidates : CandidateSource :=
    fun _ _ _ t => if Nat.eqb t 0 then [0] else [0].

  Lemma choose_candidate_source_contract :
    labeled_concrete_candidate_source_contract
      op_example_jobs
      1
      choose_example_candidates
      choose_labeled_concrete_execution.
  Proof.
    constructor.
    - intros [|t'] j Hin; simpl in *.
      + destruct Hin as [Hin | []].
        subst j.
        right. left. simpl. left. reflexivity.
      + destruct Hin as [Hin | []].
        subst j.
        right. right.
        exists 0. split; [lia|reflexivity].
    - intros [|t'] c j Hlt Hcur; simpl in *; discriminate.
    - intros [|t'] j Hin; simpl in *.
      + destruct Hin as [-> | []].
        simpl. left. reflexivity.
      + destruct Hin as [-> | []].
        simpl. left. reflexivity.
    - intros [|t'] c j Hlt Htarget; simpl in *.
      + discriminate.
      + assert (c = 0) by lia.
        subst c.
        inversion Htarget; subst.
        simpl. left. reflexivity.
    - intros s1 s2 [|t'] Hprefix; reflexivity.
  Qed.

  Definition choose_candidate_adapter_contract :
    os_local_candidate_source_adapter_contract
      choose_projection
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalCandidateSourceAdapterContract
      nat
      choose_projection
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1
      choose_local_adapter_contract
      choose_candidate_source_contract.

  Definition choose_candidate_subset (j : JobId) : Prop := j = 0.

  Lemma choose_admissible_candidate_source_contract :
    labeled_concrete_admissible_candidate_source_contract
      choose_candidate_subset
      op_example_jobs
      all_cpus_admissible
      1
      choose_example_candidates
      choose_labeled_concrete_execution.
  Proof.
    constructor.
    - exact choose_candidate_source_contract.
    - intros [|t'] j Hin; simpl in *.
      + destruct Hin as [Hin | []]. subst j. reflexivity.
      + destruct Hin as [Hin | []]. subst j. reflexivity.
    - intros [|t'] j Hsubset Helig Hadm; simpl in *.
      + unfold choose_candidate_subset in Hsubset. subst j. left. reflexivity.
      + unfold choose_candidate_subset in Hsubset. subst j. left. reflexivity.
  Qed.

  Definition choose_admissible_candidate_adapter_contract :
    os_local_admissible_candidate_source_adapter_contract
      choose_projection
      choose_candidate_subset
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalAdmissibleCandidateSourceAdapterContract
      nat
      choose_projection
      choose_candidate_subset
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1
      choose_candidate_adapter_contract
      choose_admissible_candidate_source_contract.

  Lemma choose_strong_admissible_candidate_source_contract :
    labeled_concrete_strong_admissible_candidate_source_contract
      choose_candidate_subset
      op_example_jobs
      all_cpus_admissible
      1
      choose_example_candidates
      choose_labeled_concrete_execution.
  Proof.
    constructor.
    - exact choose_admissible_candidate_source_contract.
    - intros t j Hin.
      destruct t as [|t']; simpl in Hin |- *.
      + destruct Hin as [Hin | []]. subst j.
        pose proof
          (os_local_candidate_source_adapter_contract_candidate_implies_eligible
             nat
             choose_projection
             choose_example_candidates
             op_example_jobs
             all_cpus_admissible
             1
             choose_candidate_adapter_contract
             0
             0
             (or_introl eq_refl)) as Helig.
        exact
          (admissible_somewhere_of_all_cpus_admissible
             op_example_jobs
             1
             (project_schedule
                (osl_to_op_trace choose_projection
                   (lce_trace choose_labeled_concrete_execution)))
             0
             0
             (Nat.lt_0_succ 0)
             Helig).
      + destruct Hin as [Hin | []]. subst j.
        pose proof
          (os_local_candidate_source_adapter_contract_candidate_implies_eligible
             nat
             choose_projection
             choose_example_candidates
             op_example_jobs
             all_cpus_admissible
             1
             choose_candidate_adapter_contract
             (S t')
             0
             (or_introl eq_refl)) as Helig.
        exact
          (admissible_somewhere_of_all_cpus_admissible
             op_example_jobs
             1
             (project_schedule
                (osl_to_op_trace choose_projection
                   (lce_trace choose_labeled_concrete_execution)))
             0
             (S t')
             (Nat.lt_0_succ 0)
             Helig).
  Qed.

  Definition choose_strong_admissible_candidate_adapter_contract :
    os_local_strong_admissible_candidate_source_adapter_contract
      choose_projection
      choose_candidate_subset
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalStrongAdmissibleCandidateSourceAdapterContract
      nat
      choose_projection
      choose_candidate_subset
      choose_example_candidates
      op_example_jobs
      all_cpus_admissible
      1
      choose_admissible_candidate_adapter_contract
      choose_strong_admissible_candidate_source_contract.

  Example choose_candidate_contract_choose_event_is_in_candidates :
    In 0
       (projected_candidate_list
          op_example_jobs
          1
          choose_labeled_concrete_execution
          choose_example_candidates
          0).
  Proof.
    eapply os_local_candidate_source_adapter_contract_choose_in_candidates
      with (C := choose_candidate_adapter_contract) (c := 0).
    - lia.
    - reflexivity.
  Qed.

  Example choose_candidate_contract_candidates_are_eligible :
    eligible
      op_example_jobs
      1
      (project_schedule
         (osl_to_op_trace choose_projection
            (lce_trace choose_labeled_concrete_execution)))
      0
      0.
  Proof.
    eapply os_local_candidate_source_adapter_contract_candidate_implies_eligible
      with (C := choose_candidate_adapter_contract).
    simpl. left. reflexivity.
  Qed.

  Example choose_admissible_candidate_contract_candidates_stay_in_subset :
    choose_candidate_subset 0.
  Proof.
    eapply os_local_admissible_candidate_source_adapter_contract_candidate_in_subset
      with (C := choose_admissible_candidate_adapter_contract) (t := 0).
    simpl. left. reflexivity.
  Qed.

  Example choose_strong_candidate_contract_candidates_are_admissible_somewhere :
    admissible_somewhere
      all_cpus_admissible
      op_example_jobs
      1
      (project_schedule
         (osl_to_op_trace choose_projection
            (lce_trace choose_labeled_concrete_execution)))
      0
      0.
  Proof.
    eapply os_local_strong_admissible_candidate_source_adapter_contract_candidate_somewhere
      with (C := choose_strong_admissible_candidate_adapter_contract).
    simpl. left. reflexivity.
  Qed.

  Definition example_scheduler_candidates : CandidateSource :=
    fun _ _ _ t =>
      match t with
      | 0 => []
      | 1 => [0]
      | _ => []
      end.

  Definition example_metric_algorithm : GenericSchedulingAlgorithm :=
    mkGenericSchedulingAlgorithm
      (fun jobs m sched t candidates =>
         choose_min_metric (fun _ => 0%Z) jobs m sched t candidates)
      (fun jobs m sched t candidates j Hchoose =>
         choose_min_metric_eligible (fun _ => 0%Z) jobs m sched t candidates j Hchoose)
      (fun jobs m sched t candidates Hex =>
         choose_min_metric_some_if_exists (fun _ => 0%Z) jobs m sched t candidates Hex)
      (fun jobs m sched t candidates Hnone =>
         choose_min_metric_none_if_no_eligible (fun _ => 0%Z) jobs m sched t candidates Hnone)
      (fun jobs m sched t candidates j Hchoose =>
         choose_min_metric_in_candidates (fun _ => 0%Z) jobs m sched t candidates j Hchoose).

  Lemma example_single_cpu_scheduler_relation_contract :
    labeled_concrete_single_cpu_scheduler_relation_contract
      op_example_long_jobs
      example_metric_algorithm
      example_scheduler_candidates
      example_labeled_concrete_execution.
  Proof.
    constructor.
    - intros [|[|t']]; reflexivity.
    - intros [|[|t']] c Hc; simpl.
      + destruct c; [lia|reflexivity].
      + destruct c; [lia|reflexivity].
      + destruct c; [lia|reflexivity].
  Qed.

  Example example_single_cpu_scheduler_relation :
    scheduler_rel
      (single_cpu_algorithm_schedule
         example_metric_algorithm
         example_scheduler_candidates)
      op_example_long_jobs
      1
      (project_schedule
         (osl_to_op_trace example_projection
            (lce_trace example_labeled_concrete_execution))).
  Proof.
    eapply labeled_concrete_single_cpu_scheduler_relation_contract_implies_scheduler_rel.
    exact example_single_cpu_scheduler_relation_contract.
  Qed.

  Example example_single_cpu_scheduler_relation_respects_trivial_policy :
    respects_algorithm_spec_at_with
      (fun _ _ _ _ _ _ => True)
      op_example_long_jobs
      example_scheduler_candidates
      (project_schedule
         (osl_to_op_trace example_projection
            (lce_trace example_labeled_concrete_execution)))
      1.
  Proof.
    eapply single_cpu_algorithm_schedule_respects_algorithm_spec_at_with.
    - intros jobs m sched t candidates. exact I.
    - exact example_single_cpu_scheduler_relation.
  Qed.

  Definition idle_top_m_state : OpState :=
    mkOpState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition idle_top_m_projection : OSLabeledProjection nat :=
    mkOSLabeledProjection
      nat
      (mkOSProjection nat (fun _ => idle_top_m_state))
      (fun _ _ => EvStutter).

  Definition idle_top_m_trace : concrete_trace nat := fun _ => 0.

  Lemma idle_top_m_stepwise :
    forall t,
      op_step
        (os_to_op_state (osl_to_os_projection idle_top_m_projection) (idle_top_m_trace t))
        (os_step_label idle_top_m_projection
           (idle_top_m_trace t)
           (idle_top_m_trace (S t)))
        (os_to_op_state
           (osl_to_os_projection idle_top_m_projection)
           (idle_top_m_trace (S t))).
  Proof.
    intros t.
    constructor.
  Qed.

  Lemma idle_top_m_struct_inv :
    forall t,
      op_struct_inv
        2
        (os_to_op_state
           (osl_to_os_projection idle_top_m_projection)
           (idle_top_m_trace t)).
  Proof.
    intro t.
    constructor.
    - intros j c1 c2 Hlt1 Hlt2 Hrun1 _.
      discriminate.
    - constructor.
    - intros c j Hcur Hin.
      discriminate.
    - intros j c1 c2 Hlt1 Hlt2 Ht1 _.
      discriminate.
    - intros c j Hlt Ht.
      discriminate.
  Qed.

  Definition idle_top_m_execution :
      @labeled_concrete_execution nat idle_top_m_projection 2 :=
    @mkLabeledConcreteExecution
      nat
      idle_top_m_projection
      2
      idle_top_m_trace
      True
      idle_top_m_stepwise
      idle_top_m_struct_inv.

  Definition empty_candidate_source : CandidateSource :=
    fun _ _ _ _ => [].

  Definition idle_top_m_algorithm : GenericTopMSchedulingAlgorithm :=
    make_metric_top_m_algorithm (fun _ _ => 0%Z).

  Lemma idle_top_m_scheduler_relation_contract :
    labeled_concrete_top_m_scheduler_relation_contract
      op_example_jobs
      2
      idle_top_m_algorithm
      empty_candidate_source
      idle_top_m_execution.
  Proof.
    constructor.
    intros t c.
    destruct c as [|[|c']]; reflexivity.
  Qed.

  Example idle_top_m_scheduler_relation :
    scheduler_rel
      (top_m_algorithm_schedule idle_top_m_algorithm empty_candidate_source)
      op_example_jobs
      2
      (project_schedule
         (osl_to_op_trace idle_top_m_projection
            (lce_trace idle_top_m_execution))).
  Proof.
    eapply labeled_concrete_top_m_scheduler_relation_contract_implies_scheduler_rel.
    exact idle_top_m_scheduler_relation_contract.
  Qed.

  Example choose_handoff_preserves_dispatch_target_under_stutter :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection choose_projection)
         (lce_trace choose_labeled_concrete_execution 2))
      0 = Some 0.
  Proof.
    assert (0 < 1) as Hlt by lia.
    pose proof
      (@os_local_multicore_adapter_contract_dispatch_target_preserved
         nat
         choose_projection
         op_example_jobs
         all_cpus_admissible
         1
         choose_local_adapter_contract
         1
         0
         0
         Hlt
         eq_refl) as Hpres.
    simpl in Hpres.
    apply Hpres.
    simpl.
    tauto.
  Qed.

  Lemma wakeup_local_labeled_concrete_sound :
    local_labeled_concrete_projection_sound
      op_example_jobs
      1
      wakeup_labeled_concrete_execution.
  Proof.
    constructor.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros j Hin.
      simpl in Hin.
      contradiction.
    - intros j Hin.
      simpl in Hin.
      contradiction.
    - intros [|t'] c j Hlt Hrun; simpl in *.
      + discriminate.
      + discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t; simpl in Hdispatch; discriminate.
    - intros t j Hwakeup.
      destruct t as [|t']; simpl in Hwakeup.
      + inversion Hwakeup; subst.
        unfold released, op_example_jobs, op_example_job.
        simpl.
        lia.
      + discriminate.
    - intros t j Hwakeup.
      destruct t as [|t']; simpl in Hwakeup.
      + inversion Hwakeup; subst.
        unfold completed, service_job, cpu_count, runs_on, project_schedule,
               op_example_jobs, op_example_job.
        simpl.
        lia.
      + discriminate.
    - intros t c j Hlt Hprev Hnext.
      destruct t; simpl in Hprev, Hnext; discriminate.
    - intros t c Hlt Hreq.
      destruct t; simpl in Hreq; discriminate.
    - intros t c Hlt Hhandle.
      destruct t; simpl in Hhandle; discriminate.
    - intros t c j Hlt Hchoose.
      destruct t; simpl in Hchoose; discriminate.
    - intros t c j Hlt Hchoose.
      destruct t; simpl in Hchoose; discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t; simpl in Hdispatch; discriminate.
    - intros t c j Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t j Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t c j Hlt Hblock.
      destruct t; simpl in Hblock; discriminate.
    - intros t j Hcomplete.
      destruct t as [|[|t'']]; simpl in Hcomplete; inversion Hcomplete.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t']; simpl in Hpreempt; discriminate.
  Qed.

  Example wakeup_local_contract_implies_released :
    released op_example_jobs 0 1.
  Proof.
    eapply local_labeled_concrete_projection_sound_wakeup_implies_released
      with (jobs := op_example_jobs) (ex := wakeup_labeled_concrete_execution) (t := 0) (j := 0).
    - exact wakeup_local_labeled_concrete_sound.
    - reflexivity.
  Qed.

  Lemma complete_local_labeled_concrete_sound :
    local_labeled_concrete_projection_sound
      op_example_jobs
      1
      complete_labeled_concrete_execution.
  Proof.
    constructor.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros c j Hlt Hrun.
      simpl in Hrun.
      discriminate.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
      unfold released, op_example_jobs, op_example_job.
      simpl.
      lia.
      + contradiction.
    - intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj|Hin].
      + subst j.
        apply not_completed_iff_service_lt_cost.
        unfold service_job, cpu_count, runs_on, project_schedule,
               op_example_jobs, op_example_job.
        simpl.
        lia.
      + contradiction.
    - intros [|[|t']] c j Hlt Hrun; simpl in *.
      + assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        right. left. reflexivity.
      + destruct (Nat.eqb c 0); discriminate.
      + left. exact Hrun.
    - intros t c j Hlt Hdispatch.
      destruct t as [|t'].
      + inversion Hdispatch; subst.
        unfold released, op_example_jobs, op_example_job.
        simpl.
        lia.
      + destruct t' as [|t''].
        * simpl in Hdispatch.
          discriminate.
        * simpl in Hdispatch.
          discriminate.
    - intros t j Hwakeup.
      destruct t as [|[|t'']]; simpl in Hwakeup; inversion Hwakeup.
    - intros t j Hwakeup.
      destruct t as [|[|t'']]; simpl in Hwakeup; inversion Hwakeup.
    - intros t c j Hlt Hprev Hnext.
      assert (c = 0) by lia.
      subst c.
      destruct t as [|t'].
      + simpl in Hnext.
        discriminate.
      + destruct t' as [|t''].
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hprev, Hnext.
          simpl in Hprev, Hnext.
          discriminate.
        * unfold one_cpu_state2, one_cpu_state1, one_cpu_state0 in Hprev, Hnext.
          simpl in Hprev, Hnext.
          discriminate.
    - intros t c Hlt Hreq.
      destruct t as [|t'].
      + simpl in Hreq.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hreq.
          discriminate.
        * simpl in Hreq.
          discriminate.
    - intros t c Hlt Hhandle.
      destruct t as [|t'].
      + simpl in Hhandle.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hhandle.
          discriminate.
        * simpl in Hhandle.
          discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t'].
      + simpl in Hchoose.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hchoose.
          discriminate.
        * simpl in Hchoose.
          discriminate.
    - intros t c j Hlt Hchoose.
      destruct t as [|t'].
      + simpl in Hchoose.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hchoose.
          discriminate.
        * simpl in Hchoose.
          discriminate.
    - intros t c j Hlt Hdispatch.
      destruct t as [|t'].
      + inversion Hdispatch; subst.
        unfold completed, service_job, cpu_count, runs_on, project_schedule,
               op_example_jobs, op_example_job.
        simpl.
        lia.
      + destruct t' as [|t''].
        * simpl in Hdispatch.
          discriminate.
        * simpl in Hdispatch.
          discriminate.
    - intros t c j Hblock.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hblock.
          discriminate.
        * simpl in Hblock.
          discriminate.
    - intros t j Hblock.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hblock.
          discriminate.
        * simpl in Hblock.
          discriminate.
    - intros t c j Hlt Hblock.
      destruct t as [|t'].
      + simpl in Hblock.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hblock.
          discriminate.
        * simpl in Hblock.
          discriminate.
    - intros t j Hcomplete.
      destruct t as [|t'].
      + simpl in Hcomplete.
        discriminate.
      + destruct t' as [|t''].
        * inversion Hcomplete; subst.
          unfold completed, service_job, cpu_count, runs_on, project_schedule,
                 op_example_jobs, op_example_job.
          simpl.
          lia.
        * simpl in Hcomplete.
          discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
    - intros t c old new Hlt Hpreempt.
      destruct t as [|t'].
      + simpl in Hpreempt.
        discriminate.
      + destruct t' as [|t''].
        * simpl in Hpreempt.
          discriminate.
        * simpl in Hpreempt.
          discriminate.
  Qed.

  Example complete_local_contract_implies_completed :
    completed
      op_example_jobs
      1
      (project_schedule
         (lex_trace
            (concrete_to_labeled_execution complete_labeled_concrete_execution)))
      0
      2.
  Proof.
    eapply local_labeled_concrete_projection_sound_complete_implies_completed
      with (jobs := op_example_jobs) (ex := complete_labeled_concrete_execution) (t := 1) (j := 0).
    - exact complete_local_labeled_concrete_sound.
    - reflexivity.
  Qed.

  Lemma complete_local_labeled_concrete_multicore_sound :
    local_labeled_concrete_multicore_projection_sound
      op_example_jobs
      all_cpus_admissible
      1
      complete_labeled_concrete_execution.
  Proof.
    constructor.
    - exact complete_local_labeled_concrete_sound.
    - intros [|[|t']] c Hge; simpl.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
      + destruct (Nat.eqb c 0) eqn:Ec0.
        * apply Nat.eqb_eq in Ec0. lia.
        * reflexivity.
    - intros [|[|t']] c j Hlt Hrun; simpl in *.
      + discriminate.
      + assert (c = 0) by lia.
        subst c.
        inversion Hrun; subst.
        unfold all_cpus_admissible.
        exact I.
      + destruct c; simpl in Hrun.
        * discriminate.
        * lia.
  Qed.

  Definition complete_local_adapter_contract :
    os_local_multicore_adapter_contract
      complete_projection
      op_example_jobs
      all_cpus_admissible
      1 :=
    @mkOSLocalMulticoreAdapterContract
      example_concrete_state
      complete_projection
      op_example_jobs
      all_cpus_admissible
      1
      complete_labeled_concrete_execution
      complete_local_labeled_concrete_multicore_sound.

  Example dispatch_handoff_clears_need_resched :
    op_need_resched
      (os_to_op_state
         (osl_to_os_projection example_projection)
         (lce_trace example_labeled_concrete_execution 1))
      0 = false.
  Proof.
    assert (0 < 1) as Hlt by lia.
    exact
      (@os_local_multicore_adapter_contract_dispatch_clears_need_resched
         example_concrete_state
         example_projection
         op_example_long_jobs
         all_cpus_admissible
         1
         example_local_adapter_contract
         0
         0
         0
         Hlt
         eq_refl).
  Qed.

  Example dispatch_handoff_consumes_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection example_projection)
         (lce_trace example_labeled_concrete_execution 1))
      0 = None.
  Proof.
    assert (0 < 1) as Hlt by lia.
    exact
      (@os_local_multicore_adapter_contract_dispatch_consumes_dispatch_target
         example_concrete_state
         example_projection
         op_example_long_jobs
         all_cpus_admissible
         1
         example_local_adapter_contract
         0
         0
         0
         Hlt
         eq_refl).
  Qed.

  Example block_handoff_clears_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection example_projection)
         (lce_trace example_labeled_concrete_execution 2))
      0 <> Some 0.
  Proof.
    assert (0 < 1) as Hlt by lia.
    exact
      (@os_local_multicore_adapter_contract_block_clears_dispatch_target
         example_concrete_state
         example_projection
         op_example_long_jobs
         all_cpus_admissible
         1
         example_local_adapter_contract
         1
         0
         0
         Hlt
         eq_refl).
  Qed.

  Example complete_handoff_clears_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection complete_projection)
         (lce_trace complete_labeled_concrete_execution 2))
      0 <> Some 0.
  Proof.
    assert (0 < 1) as Hlt by lia.
    exact
      (@os_local_multicore_adapter_contract_complete_clears_dispatch_target
         example_concrete_state
         complete_projection
         op_example_jobs
         all_cpus_admissible
         1
         complete_local_adapter_contract
         1
         0
         0
         Hlt
         eq_refl).
  Qed.

  Definition example_local_causality_contract :
    labeled_concrete_scheduling_causality_contract
      op_example_long_jobs
      1
      example_labeled_concrete_execution :=
    local_labeled_concrete_projection_sound_to_causality_contract
      example_concrete_state
      example_projection
      op_example_long_jobs
      1
      example_labeled_concrete_execution
      example_local_labeled_concrete_sound.

  Example dispatch_causality_sets_current :
    op_current
      (os_to_op_state
         (osl_to_os_projection example_projection)
         (lce_trace example_labeled_concrete_execution 1))
      0 = Some 0.
  Proof.
    exact (lcsc_dispatch_sets_current
             example_local_causality_contract
             0 0 0
             (Nat.lt_0_succ 0)
             eq_refl).
  Qed.

  Definition wakeup_local_causality_contract :
    labeled_concrete_scheduling_causality_contract
      op_example_jobs
      1
      wakeup_labeled_concrete_execution :=
    local_labeled_concrete_projection_sound_to_causality_contract
      nat
      wakeup_projection
      op_example_jobs
      1
      wakeup_labeled_concrete_execution
      wakeup_local_labeled_concrete_sound.

  Example wakeup_causality_makes_job_visible :
    In 0
       (op_runnable
          (os_to_op_state
             (osl_to_os_projection wakeup_projection)
             (lce_trace wakeup_labeled_concrete_execution 1))).
  Proof.
    exact (lcsc_wakeup_visible
             wakeup_local_causality_contract
             0 0
             eq_refl).
  Qed.

  Definition complete_local_causality_contract :
    labeled_concrete_scheduling_causality_contract
      op_example_jobs
      1
      complete_labeled_concrete_execution :=
    local_labeled_concrete_projection_sound_to_causality_contract
      example_concrete_state
      complete_projection
      op_example_jobs
      1
      complete_labeled_concrete_execution
      complete_local_labeled_concrete_sound.

  Example complete_causality_clears_dispatch_target :
    op_dispatch_target
      (os_to_op_state
         (osl_to_os_projection complete_projection)
         (lce_trace complete_labeled_concrete_execution 2))
      0 <> Some 0.
  Proof.
    exact (lcsc_complete_clears_dispatch_target
             complete_local_causality_contract
             1 0 0
             (Nat.lt_0_succ 0)
             eq_refl).
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
