From Stdlib Require Import List Arith Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.

Definition ev_consumes_need_resched_on (c : CPU) (ev : OpEvent) : Prop :=
  match ev with
  | EvDispatch c' _ => c' = c
  | EvPreempt c' _ _ => c' = c
  | _ => False
  end.

Definition ev_consumes_dispatch_target_on (c : CPU) (j : JobId) (ev : OpEvent) : Prop :=
  match ev with
  | EvDispatch c' j' => c' = c /\ j' = j
  | EvPreempt c' _ j' => c' = c /\ j' = j
  | EvBlock j' => j' = j
  | EvComplete j' => j' = j
  | _ => False
  end.

Record labeled_concrete_scheduler_handoff_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteSchedulerHandoffContract {
    lchc_need_resched_preserved :
      forall t c,
        c < m ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = true ->
        ~ ev_consumes_need_resched_on
            c
            (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = true;
    lchc_need_resched_cleared_by_dispatch :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = false;
    lchc_need_resched_cleared_by_preempt :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = false;
    lchc_dispatch_target_preserved :
      forall t c j,
        c < m ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        ~ ev_consumes_dispatch_target_on
            c
            j
            (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j;
    lchc_dispatch_target_consumed_by_dispatch :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = None;
    lchc_dispatch_target_consumed_by_preempt :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = None;
    lchc_dispatch_target_cleared_by_block :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvBlock j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
    lchc_dispatch_target_cleared_by_complete :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c <> Some j;
  }.

Arguments lchc_need_resched_preserved
  {CState P m ex} _ _ _ _ _.
Arguments lchc_need_resched_cleared_by_dispatch
  {CState P m ex} _ _ _ _ _.
Arguments lchc_need_resched_cleared_by_preempt
  {CState P m ex} _ _ _ _ _ _.
Arguments lchc_dispatch_target_preserved
  {CState P m ex} _ _ _ _ _ _.
Arguments lchc_dispatch_target_consumed_by_dispatch
  {CState P m ex} _ _ _ _ _.
Arguments lchc_dispatch_target_consumed_by_preempt
  {CState P m ex} _ _ _ _ _ _.
Arguments lchc_dispatch_target_cleared_by_block
  {CState P m ex} _ _ _ _ _.
Arguments lchc_dispatch_target_cleared_by_complete
  {CState P m ex} _ _ _ _ _.

Lemma local_labeled_concrete_multicore_projection_sound_to_handoff_contract :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_multicore_projection_sound jobs adm m ex ->
    labeled_concrete_scheduler_handoff_contract m ex.
Proof.
  intros CState P jobs adm m ex Hmulti.
  constructor.
  - intros t c Hlt Hneed Hnotconsume.
    pose proof (lce_stepwise ex t) as Hstep.
    destruct (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) eqn:Hev;
      inversion Hstep; subst; clear Hstep;
      simpl in *.
    + exact Hneed.
    + destruct (op_current (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) c) as [j'|] eqn:Hcur;
        simpl.
      * destruct (Nat.eqb j' j) eqn:Heq.
        -- reflexivity.
        -- exact Hneed.
      * exact Hneed.
    + destruct (op_current (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) c) as [j'|] eqn:Hcur;
        simpl.
      * destruct (Nat.eqb j' j) eqn:Heq.
        -- reflexivity.
        -- exact Hneed.
      * exact Hneed.
    + unfold set_need_resched. simpl.
      destruct (Nat.eqb_spec c0 c).
      * subst c0. rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb c c0) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. exfalso. apply n. symmetry. exact Heq.
        -- exact Hneed.
    + unfold set_need_resched. simpl.
      destruct (Nat.eqb_spec c0 c).
      * subst c0. rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb c c0) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. exfalso. apply n. symmetry. exact Heq.
        -- exact Hneed.
    + exact Hneed.
    + unfold dispatch_on_cpu, clear_need_resched, set_need_resched. simpl.
      destruct (Nat.eqb c c0) eqn:Heq.
      * apply Nat.eqb_eq in Heq. exfalso. apply Hnotconsume. symmetry. exact Heq.
      * exact Hneed.
    + unfold preempt_on_cpu, clear_need_resched, set_need_resched. simpl.
      destruct (Nat.eqb c c0) eqn:Heq.
      * apply Nat.eqb_eq in Heq. exfalso. apply Hnotconsume. symmetry. exact Heq.
      * exact Hneed.
    + exact Hneed.
    + exact Hneed.
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu, clear_need_resched, set_need_resched. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu, clear_need_resched, set_need_resched. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c j Hlt Htarget Hnotconsume.
    pose proof (lce_stepwise ex t) as Hstep.
    pose proof (lce_struct_inv ex t) as Hinv.
    destruct (os_step_label P (lce_trace ex t) (lce_trace ex (S t))) eqn:Hev;
      inversion Hstep; subst; clear Hstep;
      simpl in *.
    + exact Htarget.
    + exact Htarget.
    + exact Htarget.
    + exact Htarget.
    + exact Htarget.
    + unfold set_dispatch_target. simpl.
      destruct (Nat.eqb_spec c0 c).
      * subst c0.
        rewrite Htarget in H4.
        discriminate.
      * destruct (Nat.eqb c c0) eqn:Heq.
        -- apply Nat.eqb_eq in Heq. exfalso. apply n. symmetry. exact Heq.
        -- exact Htarget.
    + unfold dispatch_on_cpu, clear_dispatch_target, set_dispatch_target. simpl.
      destruct (Nat.eqb c c0) eqn:Heq; simpl in *.
      * apply Nat.eqb_eq in Heq. subst c0.
        match goal with
        | Hpending :
            op_dispatch_target
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) c =
            Some ?jpending |- _ =>
            rewrite Htarget in Hpending;
            inversion Hpending; subst
        end.
        exfalso. apply Hnotconsume. split; reflexivity.
      * exact Htarget.
    + unfold preempt_on_cpu, clear_dispatch_target, set_dispatch_target. simpl.
      destruct (Nat.eqb c c0) eqn:Heq; simpl in *.
      * apply Nat.eqb_eq in Heq. subst c0.
        match goal with
        | Hpending :
            op_dispatch_target
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) c =
            Some ?jpending |- _ =>
            rewrite Htarget in Hpending;
            inversion Hpending; subst
        end.
        exfalso. apply Hnotconsume. split; reflexivity.
      * exact Htarget.
    + exact Htarget.
    + exact Htarget.
  - intros t c j Hlt Hdispatch.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hdispatch in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold dispatch_on_cpu, clear_dispatch_target, set_dispatch_target. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c old new Hlt Hpreempt.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hpreempt in Hstep.
    inversion Hstep; subst; clear Hstep.
    unfold preempt_on_cpu, clear_dispatch_target, set_dispatch_target. simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - intros t c j Hlt Hblock.
    exact (llcps_block_clears_dispatch_target (llcmps_projection_sound Hmulti) t c j Hlt Hblock).
  - intros t c j Hlt Hcomplete.
    pose proof (lce_stepwise ex t) as Hstep.
    rewrite Hcomplete in Hstep.
    inversion Hstep; subst; clear Hstep.
    pose proof (lce_struct_inv ex t) as Hinv.
    destruct Hinv as [_ _ Hnotin _ Hdispatch].
    intros Htarget.
    pose proof (Hdispatch c j Hlt Htarget) as Hin.
    match goal with
    | Hrun :
        op_job_running
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)) j |- _ =>
        destruct Hrun as [c_run Hcur];
        exact ((Hnotin c_run j Hcur) Hin)
    end.
Qed.

Definition os_local_scheduler_handoff_contract
    {CState : Type}
    {P : OSLabeledProjection CState}
    {jobs : JobId -> Job}
    {adm : admissible_cpu}
    {m : nat}
    (C : os_local_multicore_adapter_contract P jobs adm m)
  : labeled_concrete_scheduler_handoff_contract m (olac_execution C) :=
  local_labeled_concrete_multicore_projection_sound_to_handoff_contract
    CState P jobs adm m (olac_execution C) (olac_sound C).
