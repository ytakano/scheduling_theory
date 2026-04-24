From Stdlib Require Import List Arith.PeanoNat Lia Compare_dec.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
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
From RocqSched Require Import Operational.Common.OSCausalityContract.

Definition op_job_visible (m : nat) (st : OpState) (j : JobId) : Prop :=
  (exists c, c < m /\ op_current st c = Some j) \/
  In j (op_runnable st) \/
  exists c, c < m /\ op_dispatch_target st c = Some j.

Lemma released_monotone :
  forall jobs j t1 t2,
    t1 <= t2 ->
    released jobs j t1 ->
    released jobs j t2.
Proof.
  intros jobs j t1 t2 Hle Hrel.
  unfold released in *.
  lia.
Qed.

Lemma projected_job_not_running_if_runnable :
  forall m st j t,
    op_struct_inv m st ->
    In j (op_runnable st) ->
    ~ running m (project_schedule (fun _ => st)) j t.
Proof.
  intros m st j t Hinv Hin [c [Hlt Hrun]].
  destruct Hinv as [_ _ Hnotin _ _].
  apply (Hnotin c j Hrun).
  exact Hin.
Qed.

Lemma projected_trace_job_not_running_if_runnable :
  forall m tr j t,
    op_struct_inv m (tr t) ->
    In j (op_runnable (tr t)) ->
    ~ running m (project_schedule tr) j t.
Proof.
  intros m tr j t Hinv Hin.
  unfold running, project_schedule.
  intros [c [Hlt Hrun]].
  destruct Hinv as [_ _ Hnotin _ _].
  apply (Hnotin c j Hrun).
  exact Hin.
Qed.

Lemma visible_job_not_completed_if_not_running_next :
  forall jobs m sched j t,
    ~ completed jobs m sched j t ->
    ~ running m sched j t ->
    ~ completed jobs m sched j (S t).
Proof.
  intros jobs m sched j t Hncomp Hnotrun HcompS.
  apply (proj1 (not_completed_iff_service_lt_cost jobs m sched j t)) in Hncomp.
  apply (proj1 (completed_iff_service_ge_cost jobs m sched j (S t))) in HcompS.
  rewrite service_job_no_increase_if_not_executed in HcompS.
  - lia.
  - intros c Hlt Hcur.
    apply Hnotrun.
    exists c. split; assumption.
Qed.

Record labeled_concrete_scheduler_view_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteSchedulerViewContract {
    lcsv_visible_released :
      forall t j,
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          j ->
        released jobs j t;
    lcsv_visible_not_completed :
      forall t j,
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          j ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            j t;
    lcsv_wakeup_visible :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvWakeup j ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          j;
    lcsv_choose_visible :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          j;
    lcsv_dispatch_visible :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          j;
    lcsv_preempt_old_visible :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          old;
    lcsv_preempt_new_visible :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_job_visible
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          new;
    lcsv_block_clears_current :
      forall t c j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvBlock j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
    lcsv_block_clears_runnable :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvBlock j ->
        ~ In j
             (op_runnable
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsv_block_clears_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvBlock j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
    lcsv_complete_sets_completed :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        completed
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j (S t);
    lcsv_complete_clears_current :
      forall t c j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
    lcsv_complete_clears_runnable :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        ~ In j
             (op_runnable
                (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t))));
    lcsv_complete_clears_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
  }.

Arguments lcsv_visible_released
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_visible_not_completed
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_wakeup_visible
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_choose_visible
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsv_dispatch_visible
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcsv_preempt_old_visible
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsv_preempt_new_visible
  {CState P jobs m ex} _ _ _ _ _ _ _.
Arguments lcsv_block_clears_current
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsv_block_clears_runnable
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_block_clears_dispatch_target
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsv_complete_sets_completed
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_complete_clears_current
  {CState P jobs m ex} _ _ _ _ _.
Arguments lcsv_complete_clears_runnable
  {CState P jobs m ex} _ _ _ _.
Arguments lcsv_complete_clears_dispatch_target
  {CState P jobs m ex} _ _ _ _ _.

Lemma local_labeled_concrete_projection_sound_current_released :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_projection_sound jobs m ex ->
    forall t c j,
      c < m ->
      op_current
        (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
        c = Some j ->
      released jobs j t.
Proof.
  intros CState P jobs m ex Hlocal.
  induction t as [|t IH]; intros c j Hlt Hrun.
  - exact (llcps_init_release Hlocal c j Hlt Hrun).
  - destruct (llcps_current_origin Hlocal t c j Hlt Hrun) as [Hprev | [Hdispatch | Hpreempt]].
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH c j Hlt Hprev)).
    + exact (llcps_dispatch_release Hlocal t c j Hlt Hdispatch).
    + destruct Hpreempt as [old Hpreempt].
      exact (llcps_preempt_release Hlocal t c old j Hlt Hpreempt).
Qed.

Lemma local_labeled_concrete_projection_sound_current_not_completed :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_projection_sound jobs m ex ->
    forall t c j,
      c < m ->
      op_current
        (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
        c = Some j ->
      ~ completed
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j t.
Proof.
  intros CState P jobs m ex Hlocal.
  induction t as [|t IH]; intros c j Hlt Hrun.
  - exact (llcps_init_completion Hlocal c j Hlt Hrun).
  - destruct (llcps_current_origin Hlocal t c j Hlt Hrun) as [Hprev | [Hdispatch | Hpreempt]].
    + exact (llcps_persistent_completion Hlocal t c j Hlt Hprev Hrun).
    + exact (llcps_dispatch_completion Hlocal t c j Hlt Hdispatch).
    + destruct Hpreempt as [old Hpreempt].
      exact (llcps_preempt_completion Hlocal t c old j Hlt Hpreempt).
Qed.

Lemma local_labeled_concrete_multicore_projection_sound_runnable_released :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_multicore_projection_sound jobs adm m ex ->
    forall t j,
      In j
         (op_runnable
            (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))) ->
      released jobs j t.
Proof.
  intros CState P jobs adm m ex Hmulti.
  induction t as [|t IH]; intros j Hin.
  - exact (llcps_init_runnable_release (llcmps_projection_sound Hmulti) j Hin).
  - pose proof (lce_stepwise ex t) as Hstep.
    destruct (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) eqn:Hev;
      inversion Hstep; subst; clear Hstep;
      repeat match goal with
      | Hstate : _ = os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)) |- _ =>
          rewrite <- Hstate in Hin
      | Hstate : os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)) = _ |- _ =>
          rewrite Hstate in Hin
      end;
      simpl in Hin.
    + destruct Hin as [->|Hin].
      * exact (llcps_wakeup_release (llcmps_projection_sound Hmulti) t j Hev).
      * exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + apply remove_job_in in Hin as [Hin _].
      exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + apply remove_job_in in Hin as [Hin _].
      exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + apply remove_job_in in Hin as [Hin _].
      exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + destruct Hin as [Heq|Hin].
      * subst j.
        assert (Hltc : c < m).
        { destruct (lt_dec c m) as [Hltc|Hge]; auto.
          assert (m <= c) by lia.
          pose proof (llcmps_idle_outside Hmulti t c H) as Hid.
          rewrite H4 in Hid.
          discriminate. }
        pose proof
          (local_labeled_concrete_projection_sound_current_released
             CState P jobs m ex (llcmps_projection_sound Hmulti) t c old Hltc H4) as Hrel_old.
        exact (released_monotone jobs old t (S t) (Nat.le_succ_diag_r t) Hrel_old).
      * apply remove_job_in in Hin as [Hin _].
        exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
    + exact (released_monotone jobs j t (S t) (Nat.le_succ_diag_r t) (IH j Hin)).
Qed.

Lemma local_labeled_concrete_multicore_projection_sound_runnable_not_completed :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_multicore_projection_sound jobs adm m ex ->
    forall t j,
      In j
         (op_runnable
            (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))) ->
      ~ completed
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j t.
Proof.
  intros CState P jobs adm m ex Hmulti.
  induction t as [|t IH]; intros j Hin.
  - exact (llcps_init_runnable_completion (llcmps_projection_sound Hmulti) j Hin).
  - pose proof (lce_stepwise ex t) as Hstep.
    pose proof (lce_struct_inv ex t) as Hinv.
    destruct (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) eqn:Hev;
      inversion Hstep; subst; clear Hstep;
      repeat match goal with
      | Hstate : _ = os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)) |- _ =>
          rewrite <- Hstate in Hin
      | Hstate : os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)) = _ |- _ =>
          rewrite Hstate in Hin
      end;
      simpl in Hin.
    + destruct Hin as [->|Hin].
      * exact (llcps_wakeup_completion (llcmps_projection_sound Hmulti) t j Hev).
      * eapply visible_job_not_completed_if_not_running_next.
        -- exact (IH j Hin).
        -- eapply projected_trace_job_not_running_if_runnable; eauto.
    + apply remove_job_in in Hin as [Hin _].
      eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + apply remove_job_in in Hin as [Hin _].
      eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + apply remove_job_in in Hin as [Hin _].
      eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + destruct Hin as [Heq|Hin].
      * subst j.
        assert (Hltc : c < m).
        { destruct (lt_dec c m) as [Hltc|Hge]; auto.
          assert (m <= c) by lia.
          pose proof (llcmps_idle_outside Hmulti t c H) as Hid.
          rewrite H4 in Hid.
          discriminate. }
        exact (llcps_preempt_old_completion (llcmps_projection_sound Hmulti) t c old new Hltc Hev).
      * apply remove_job_in in Hin as [Hin _].
        eapply visible_job_not_completed_if_not_running_next.
        -- exact (IH j Hin).
        -- eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
    + eapply visible_job_not_completed_if_not_running_next.
      * exact (IH j Hin).
      * eapply projected_trace_job_not_running_if_runnable; eauto.
Qed.

Lemma local_labeled_concrete_multicore_projection_sound_to_scheduler_view_contract :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_multicore_projection_sound jobs adm m ex ->
    labeled_concrete_scheduling_causality_contract jobs m ex ->
    labeled_concrete_scheduler_view_contract jobs m ex.
Proof.
  intros CState P jobs adm m ex Hmulti Hcaus.
  constructor.
  - intros t j [[c [Hlt Hcur]] | [Hin | [c [Hlt Htarget]]]].
    + eapply local_labeled_concrete_projection_sound_current_released; eauto.
      exact (llcmps_projection_sound Hmulti).
    + eapply local_labeled_concrete_multicore_projection_sound_runnable_released; eauto.
    + pose proof (lce_struct_inv ex t) as Hinv.
      destruct Hinv as [_ _ _ _ Hdispatch].
      pose proof (Hdispatch c j Hlt Htarget) as Hin.
      eapply local_labeled_concrete_multicore_projection_sound_runnable_released; eauto.
  - intros t j [[c [Hlt Hcur]] | [Hin | [c [Hlt Htarget]]]].
    + eapply local_labeled_concrete_projection_sound_current_not_completed; eauto.
      exact (llcmps_projection_sound Hmulti).
    + eapply local_labeled_concrete_multicore_projection_sound_runnable_not_completed; eauto.
    + pose proof (lce_struct_inv ex t) as Hinv.
      destruct Hinv as [_ _ _ _ Hdispatch].
      pose proof (Hdispatch c j Hlt Htarget) as Hin.
      eapply local_labeled_concrete_multicore_projection_sound_runnable_not_completed; eauto.
  - intros t j Hwakeup.
    right. left.
    exact (lcsc_wakeup_visible Hcaus t j Hwakeup).
  - intros t c j Hlt Hchoose.
    right. right. exists c. split.
    + exact Hlt.
    + exact (lcsc_choose_sets_dispatch_target Hcaus t c j Hlt Hchoose).
  - intros t c j Hlt Hdispatch.
    left. exists c. split; [exact Hlt|].
    exact (lcsc_dispatch_sets_current Hcaus t c j Hlt Hdispatch).
  - intros t c old new Hlt Hpreempt.
    right. left.
    exact (lcsc_preempt_requeues_old Hcaus t c old new Hlt Hpreempt).
  - intros t c old new Hlt Hpreempt.
    left. exists c. split; [exact Hlt|].
    exact (lcsc_preempt_sets_current Hcaus t c old new Hlt Hpreempt).
  - intros t c j Hblock.
    exact (llcps_block_clears_current (llcmps_projection_sound Hmulti) t c j Hblock).
  - intros t j Hblock.
    exact (llcps_block_clears_runnable (llcmps_projection_sound Hmulti) t j Hblock).
  - intros t c j Hlt Hblock.
    exact (llcps_block_clears_dispatch_target (llcmps_projection_sound Hmulti) t c j Hlt Hblock).
  - intros t j Hcomplete.
    exact (lcsc_complete_sets_completed Hcaus t j Hcomplete).
  - intros t c j Hcomplete.
    exact (lcsc_complete_clears_current Hcaus t c j Hcomplete).
  - intros t j Hcomplete.
    exact (lcsc_complete_clears_runnable Hcaus t j Hcomplete).
  - intros t c j Hlt Hcomplete.
    exact (lcsc_complete_clears_dispatch_target Hcaus t c j Hlt Hcomplete).
Qed.

Definition os_local_scheduler_view_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    {jobs : JobId -> Job}
    {adm : admissible_cpu}
    {m : nat}
    (C : os_local_multicore_adapter_contract P jobs adm m) : Prop :=
  labeled_concrete_scheduler_view_contract jobs m (olac_execution C).

Lemma os_local_multicore_adapter_contract_to_scheduler_view_contract :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m),
    os_local_scheduler_view_contract C.
Proof.
  intros CState P jobs adm m C.
  unfold os_local_scheduler_view_contract.
  eapply local_labeled_concrete_multicore_projection_sound_to_scheduler_view_contract.
  - exact (olac_sound C).
  - apply os_local_multicore_adapter_contract_to_causality_contract.
Qed.
