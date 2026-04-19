From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.StepLemmas.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.

Lemma op_running_job_not_dispatch_pending_in_range :
  forall m st c_run j c,
    op_struct_inv m st ->
    op_current st c_run = Some j ->
    c < m ->
    op_dispatch_target st c <> Some j.
Proof.
  intros m st c_run j c Hinv Hcur Hlt Hpending.
  destruct Hinv as [_ _ Hnotin _ Hdispatchrun].
  pose proof (Hnotin c_run j Hcur) as Hnotrunnable.
  pose proof (Hdispatchrun c j Hlt Hpending) as Hin.
  contradiction.
Qed.

Record labeled_concrete_scheduling_causality_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteSchedulingCausalityContract {
    lcsc_wakeup_released :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvWakeup j ->
        released jobs j (S t);
    lcsc_wakeup_visible :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvWakeup j ->
        In j
           (op_runnable
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsc_request_sets_need_resched :
      forall t c,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvRequestResched c ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = true;
    lcsc_handle_sets_need_resched :
      forall t c,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvHandleResched c ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = true;
    lcsc_choose_sets_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j;
    lcsc_choose_from_runnable :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
        In j
           (op_runnable
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)));
    lcsc_dispatch_sets_current :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j;
    lcsc_dispatch_clears_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = None;
    lcsc_dispatch_clears_need_resched :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = false;
    lcsc_dispatch_removes_from_runnable :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        ~ In j
             (op_runnable
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsc_preempt_sets_current :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some new;
    lcsc_preempt_requeues_old :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        In old
           (op_runnable
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsc_preempt_removes_new_from_runnable :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        ~ In new
             (op_runnable
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsc_preempt_clears_dispatch_target :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = None;
    lcsc_preempt_clears_need_resched :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = false;
    lcsc_complete_sets_completed :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        completed
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j (S t);
    lcsc_complete_clears_current :
      forall t c j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
    lcsc_complete_clears_runnable :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        ~ In j
             (op_runnable
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsc_complete_clears_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
  }.

Arguments lcsc_wakeup_released
  {CState P jobs m ex} _ _ _ _.
Arguments lcsc_wakeup_visible
  {CState P jobs m ex} _ _ _ _.
Arguments lcsc_request_sets_need_resched
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsc_handle_sets_need_resched
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsc_choose_sets_dispatch_target
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_choose_from_runnable
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_dispatch_sets_current
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_dispatch_clears_dispatch_target
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_dispatch_clears_need_resched
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_dispatch_removes_from_runnable
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsc_preempt_sets_current
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsc_preempt_requeues_old
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsc_preempt_removes_new_from_runnable
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsc_preempt_clears_dispatch_target
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsc_preempt_clears_need_resched
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsc_complete_sets_completed
  {CState P jobs m ex} _ _ _ _.
Arguments lcsc_complete_clears_current
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsc_complete_clears_runnable
  {CState P jobs m ex} _ _ _ _.
Arguments lcsc_complete_clears_dispatch_target
  {CState P jobs m ex} _ _ _ _ _.

Lemma local_labeled_concrete_projection_sound_to_causality_contract :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_projection_sound jobs m ex ->
    labeled_concrete_scheduling_causality_contract jobs m ex.
Proof.
  intros CState P jobs m ex Hlocal.
  constructor.
  - intros t j Hwakeup.
    exact (llcps_wakeup_release Hlocal t j Hwakeup).
  - intros t j Hwakeup.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hwakeup in Hstep.
    inversion Hstep; subst; clear Hstep.
    simpl. left. reflexivity.
  - intros t c Hlt Hreq.
    exact (llcps_request_sets_need_resched Hlocal t c Hlt Hreq).
  - intros t c Hlt Hhandle.
    exact (llcps_handle_sets_need_resched Hlocal t c Hlt Hhandle).
  - intros t c j Hlt Hchoose.
    exact (llcps_choose_sets_dispatch_target Hlocal t c j Hlt Hchoose).
  - intros t c j Hlt Hchoose.
    exact (llcps_choose_from_runnable Hlocal t c j Hlt Hchoose).
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu. simpl.
    apply remove_job_not_in.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu. simpl.
    left. reflexivity.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu. simpl.
    intros [Heq | Hin].
    + contradiction.
    + eapply remove_job_not_in; eauto.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t j Hcomplete.
    exact (llcps_complete_sets_completed Hlocal t j Hcomplete).
  - intros t c j Hcomplete Hcur.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hcomplete in Hstep.
    inversion Hstep; subst; clear Hstep.
    rewrite <- H1 in Hcur.
    unfold clear_current_and_request in Hcur. simpl in Hcur.
    destruct (op_current
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) c)
      as [j'|] eqn:Hcur_prev.
    + destruct (Nat.eqb_spec j' j); congruence.
    + inversion Hcur.
  - intros t j Hcomplete.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hcomplete in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold clear_current_and_request. simpl.
    apply remove_job_not_in.
  - intros t c j Hlt Hcomplete Htarget.
    pose proof (lce_stepwise ex t) as Hstep.
    pose proof (lce_struct_inv ex t) as Hinv.
    rewrite Hcomplete in Hstep.
    inversion Hstep; subst; clear Hstep.
    destruct H2 as [c_run Hrun].
    rewrite <- H1 in Htarget.
    unfold clear_current_and_request in Htarget. simpl in Htarget.
    eapply
      (op_running_job_not_dispatch_pending_in_range
         m
         (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
         c_run j c); eauto.
Qed.

Definition os_local_scheduling_causality_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    {jobs : JobId -> Job}
    {adm : admissible_cpu}
    {m : nat}
    (C : os_local_multicore_adapter_contract P jobs adm m) : Prop :=
  labeled_concrete_scheduling_causality_contract jobs m (olac_execution C).

Lemma os_local_multicore_adapter_contract_to_causality_contract :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m),
    os_local_scheduling_causality_contract C.
Proof.
  intros CState P jobs adm m C.
  unfold os_local_scheduling_causality_contract.
  apply local_labeled_concrete_projection_sound_to_causality_contract.
  exact (llcmps_projection_sound (olac_sound C)).
Qed.
