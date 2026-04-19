From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.ProjectionInvariants.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
Import ListNotations.

Lemma remove_job_in :
  forall j x xs,
    In x (remove_job j xs) ->
    In x xs /\ x <> j.
Proof.
  intros j x xs.
  induction xs as [|y ys IH]; simpl.
  - intros [].
  - destruct (Nat.eqb y j) eqn:Hy.
    + intros Hrem.
      specialize (IH Hrem) as [Hin_tail Hneq].
      split; [right; exact Hin_tail|exact Hneq].
    + intros [->|Hrem].
      * split.
        -- left. reflexivity.
        -- apply Nat.eqb_neq in Hy. exact Hy.
      * specialize (IH Hrem) as [Hin' Hneq].
        split; [right; exact Hin'|exact Hneq].
Qed.

Lemma remove_job_not_in :
  forall j xs,
    ~ In j (remove_job j xs).
Proof.
  intros j xs Hin.
  apply remove_job_in in Hin as [_ Hneq].
  contradiction.
Qed.

Lemma remove_job_preserves_NoDup :
  forall j xs,
    NoDup xs ->
    NoDup (remove_job j xs).
Proof.
  intros j xs Hnd.
  induction Hnd as [|x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (Nat.eqb x j) eqn:Hxj.
    + exact IH.
    + constructor.
      * intros Hin.
        apply remove_job_in in Hin as [Hin _].
        contradiction.
      * exact IH.
Qed.

Lemma remove_job_preserves_member :
  forall j x xs,
    In x xs ->
    x <> j ->
    In x (remove_job j xs).
Proof.
  intros j x xs Hin Hneq.
  induction xs as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + destruct (Nat.eqb y j) eqn:Hxj.
      * apply Nat.eqb_eq in Hxj. contradiction.
      * left. reflexivity.
    + destruct (Nat.eqb y j) eqn:Hy.
      * apply IH; assumption.
      * right. apply IH; assumption.
Qed.

Lemma op_job_running_current :
  forall st j,
    op_job_running st j ->
    exists c, op_current st c = Some j.
Proof.
  intros st j [c Hcur].
  exists c. exact Hcur.
Qed.

Definition op_step_sound_pre (st : OpState) (ev : OpEvent) : Prop :=
  match ev with
  | EvWakeup j =>
      ~ In j (op_runnable st) /\
      ~ op_job_running st j /\
      ~ op_job_dispatch_pending st j
  | _ => True
  end.

Definition op_step_range_pre (m : nat) (ev : OpEvent) : Prop :=
  match ev with
  | EvRequestResched c => c < m
  | EvHandleResched c => c < m
  | EvChoose c _ => c < m
  | EvDispatch c _ => c < m
  | EvPreempt c _ _ => c < m
  | _ => True
  end.

Definition op_step_placement_pre
    (adm : admissible_cpu) (m : nat) (st : OpState) (ev : OpEvent) : Prop :=
  match ev with
  | EvDispatch c j => c < m /\ adm j c
  | EvPreempt c _ j => c < m /\ adm j c
  | _ => True
  end.

Lemma add_runnable_preserves_struct_inv :
  forall m st j,
    op_struct_inv m st ->
    ~ In j (op_runnable st) ->
    ~ op_job_running st j ->
    ~ op_job_dispatch_pending st j ->
    op_struct_inv m (add_runnable j st).
Proof.
  intros m st j Hinv Hnotin Hnotrunning Hnotpending.
  destruct Hinv as [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  constructor.
  - exact Hdup.
  - simpl. constructor; assumption.
  - intros c j' Hcur.
    simpl.
    intros [Heq|Hin].
    + subst j'.
      apply Hnotrunning.
      exists c. exact Hcur.
    + eapply Hsep; eauto.
  - intros j' c1 c2 Hlt1 Hlt2 Ht1 Ht2.
    eapply Hdispatchdup; eauto.
  - intros c j' Hlt Ht.
    simpl in Ht.
    right.
    eapply Hdispatchrun; eauto.
Qed.

Lemma clear_current_and_request_preserves_struct_inv :
  forall m st j,
    op_struct_inv m st ->
    op_job_running st j ->
    op_struct_inv m (clear_current_and_request j st).
Proof.
  intros m st j Hinv Hrunning.
  destruct Hinv as [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  destruct Hrunning as [crun Hrun].
  constructor.
  - intros j' c1 c2 Hlt1 Hlt2 Hcur1 Hcur2.
    simpl in Hcur1, Hcur2.
    destruct (op_current st c1) as [k1|] eqn:Hc1; try discriminate.
    destruct (Nat.eqb k1 j) eqn:Ek1; try discriminate.
    destruct (op_current st c2) as [k2|] eqn:Hc2; try discriminate.
    destruct (Nat.eqb k2 j) eqn:Ek2; try discriminate.
    inversion Hcur1; inversion Hcur2; subst.
    eapply Hdup; eauto.
  - simpl. apply remove_job_preserves_NoDup. exact Hnodup.
  - intros c j'.
    intros Hcur Hin.
    simpl in Hcur.
    destruct (op_current st c) as [k|] eqn:Hc; try discriminate.
    destruct (Nat.eqb k j) eqn:Ek; try discriminate.
    inversion Hcur; subst.
    apply remove_job_in in Hin as [Hin' _].
    eapply Hsep; eauto.
  - intros j' c1 c2 Hlt1 Hlt2 Ht1 Ht2.
    simpl in Ht1, Ht2.
    eapply Hdispatchdup; eauto.
  - intros c j' Hlt Ht.
    simpl in Ht.
    specialize (Hdispatchrun c j' Hlt Ht) as Hin.
    assert (j' <> j).
    { intros ->.
      eapply Hsep in Hin; eauto. }
    apply remove_job_preserves_member; assumption.
Qed.

Lemma set_need_resched_preserves_struct_inv :
  forall m st c b,
    op_struct_inv m st ->
    op_struct_inv m (set_need_resched c b st).
Proof.
  intros m st c b [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  constructor; simpl; assumption.
Qed.

Lemma choose_preserves_struct_inv :
  forall m st c j,
    op_struct_inv m st ->
    In j (op_runnable st) ->
    op_dispatch_target st c = None ->
    ~ op_job_dispatch_pending st j ->
    c < m ->
    op_struct_inv m (set_dispatch_target c (Some j) st).
Proof.
  intros m st c j Hinv Hinj Hslot Hnotpending Hltc.
  destruct Hinv as [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  constructor.
  - exact Hdup.
  - exact Hnodup.
  - intros c' j' Hcur.
    simpl.
    exact (Hsep c' j' Hcur).
  - intros j' c1 c2 Hlt1 Hlt2 Ht1 Ht2.
    simpl in Ht1, Ht2.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_eq in Ec2.
      lia.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_neq in Ec2.
      subst c1.
      inversion Ht1; subst j'.
      exfalso.
      apply Hnotpending.
      exists c2. exact Ht2.
    + apply Nat.eqb_neq in Ec1.
      apply Nat.eqb_eq in Ec2.
      subst c2.
      inversion Ht2; subst j'.
      exfalso.
      apply Hnotpending.
      exists c1. exact Ht1.
    + eapply Hdispatchdup; eauto.
  - intros c' j' Hlt Ht.
    simpl in Ht.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c'.
      inversion Ht; subst.
      exact Hinj.
    + eapply Hdispatchrun; eauto.
Qed.

Lemma dispatch_preserves_struct_inv :
  forall m st c j,
    op_struct_inv m st ->
    op_dispatch_target st c = Some j ->
    op_current st c = None ->
    c < m ->
    op_struct_inv
      m
      (clear_need_resched c
         (clear_dispatch_target c
            (mkOpState
               (fun c' => if Nat.eqb c' c then Some j else op_current st c')
               (remove_job j (op_runnable st))
               (op_need_resched st)
               (op_dispatch_target st)))).
Proof.
  intros m st c j Hinv Htarget Hnone Hltc.
  destruct Hinv as [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  constructor.
  - intros j' c1 c2 Hlt1 Hlt2 Hcur1 Hcur2.
    simpl in Hcur1, Hcur2.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_eq in Ec2.
      lia.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_neq in Ec2.
      subst c1.
      inversion Hcur1; subst j'.
      exfalso.
      pose proof (Hdispatchrun c j Hltc Htarget) as Hinj.
      eapply Hsep in Hinj; eauto.
    + apply Nat.eqb_neq in Ec1.
      apply Nat.eqb_eq in Ec2.
      subst c2.
      inversion Hcur2; subst j'.
      exfalso.
      pose proof (Hdispatchrun c j Hltc Htarget) as Hinj.
      eapply Hsep in Hinj; eauto.
    + eapply Hdup; eauto.
  - simpl. apply remove_job_preserves_NoDup. exact Hnodup.
  - intros c' j' Hcur Hin'.
    simpl in Hcur.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c'.
      inversion Hcur; subst j'.
      exact (remove_job_not_in j (op_runnable st) Hin').
    + apply Nat.eqb_neq in Ecc.
      eapply Hsep; eauto.
      apply remove_job_in in Hin' as [Hin'' _].
      exact Hin''.
  - intros j' c1 c2 Hlt1 Hlt2 Ht1 Ht2.
    simpl in Ht1, Ht2.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2; try discriminate.
    eapply Hdispatchdup; eauto.
  - intros c' j' Hlt' Ht.
    simpl in Ht.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + discriminate.
    + assert (Hin_old : In j' (op_runnable st)).
      { eapply Hdispatchrun; eauto. }
      assert (j' <> j).
      { intros Heq.
        subst j'.
        apply Nat.eqb_neq in Ecc.
        pose proof (Hdispatchdup j c c' Hltc Hlt' Htarget Ht) as Heqcc.
        lia.
      }
      apply remove_job_preserves_member; assumption.
Qed.

Lemma preempt_preserves_struct_inv :
  forall m st c old new,
    op_struct_inv m st ->
    op_current st c = Some old ->
    (forall c', op_current st c' = Some old -> c' = c) ->
    op_dispatch_target st c = Some new ->
    old <> new ->
    c < m ->
    op_struct_inv m (preempt_on_cpu c old new st).
Proof.
  intros m st c old new Hinv Hcurrent Hunique Htarget Hneq Hltc.
  destruct Hinv as [Hdup Hnodup Hsep Hdispatchdup Hdispatchrun].
  assert (Hold_notin : ~ In old (op_runnable st)).
  { eapply Hsep; eauto. }
  assert (Hnew_in : In new (op_runnable st)).
  { eapply Hdispatchrun; eauto. }
  constructor.
  - intros j c1 c2 Hlt1 Hlt2 Hcur1 Hcur2.
    simpl in Hcur1, Hcur2.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_eq in Ec2.
      lia.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_neq in Ec2.
      subst c1.
      inversion Hcur1; subst j.
      exfalso.
      eapply Hsep; eauto.
    + apply Nat.eqb_neq in Ec1.
      apply Nat.eqb_eq in Ec2.
      subst c2.
      inversion Hcur2; subst j.
      exfalso.
      eapply Hsep; eauto.
    + eapply Hdup; eauto.
  - simpl.
    constructor.
    + intros Hin.
      apply remove_job_in in Hin as [Hin' _].
      contradiction.
    + apply remove_job_preserves_NoDup.
      exact Hnodup.
  - intros c' j Hcur Hin.
    simpl in Hcur.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc.
      subst c'.
      inversion Hcur; subst j.
      destruct Hin as [Heq_old | Hin_new].
      * contradiction.
      * exact (remove_job_not_in new (op_runnable st) Hin_new).
    + apply Nat.eqb_neq in Ecc.
      destruct Hin as [Heq_old | Hin_new].
      * subst j.
        exfalso.
        pose proof (Hunique c' Hcur) as Heqcc.
        contradiction.
      * apply remove_job_in in Hin_new as [Hin_old _].
        eapply (Hsep c' j Hcur).
        exact Hin_old.
  - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
    simpl in Ht1, Ht2.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2; try discriminate.
    eapply Hdispatchdup; eauto.
  - intros c' j Hlt' Ht.
    simpl in Ht.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + discriminate.
    + assert (Hin_old : In j (op_runnable st)).
      { eapply Hdispatchrun; eauto. }
      assert (j <> new).
      { intros Heq.
        subst j.
        apply Nat.eqb_neq in Ecc.
        pose proof (Hdispatchdup new c c' Hltc Hlt' Htarget Ht) as Heqcc.
        lia.
      }
      right.
      apply remove_job_preserves_member; assumption.
Qed.

Lemma op_step_preserves_struct_inv :
  forall m st ev st',
    op_struct_inv m st ->
    op_step_sound_pre st ev ->
    op_step_range_pre m ev ->
    op_step st ev st' ->
    op_struct_inv m st'.
Proof.
  intros m st ev st' Hinv Hpre Hrange Hstep.
  inversion Hstep; subst; clear Hstep.
  - destruct Hpre as [Hnotin [Hnotrunning Hnotpending]].
    apply add_runnable_preserves_struct_inv; assumption.
  - eapply clear_current_and_request_preserves_struct_inv; eauto.
  - eapply clear_current_and_request_preserves_struct_inv; eauto.
  - apply set_need_resched_preserves_struct_inv; assumption.
  - apply set_need_resched_preserves_struct_inv; assumption.
  - eapply choose_preserves_struct_inv; eauto.
  - eapply dispatch_preserves_struct_inv; eauto.
  - eapply preempt_preserves_struct_inv; eauto.
  - exact Hinv.
  - exact Hinv.
Qed.

Lemma op_step_preserves_idle_outside_range :
  forall m st ev st',
    op_idle_outside_range m st ->
    op_step_range_pre m ev ->
    op_step st ev st' ->
    op_idle_outside_range m st'.
Proof.
  intros m st ev st' Hid Hpre Hstep c Hge.
  inversion Hstep; subst; clear Hstep; simpl.
  - exact (Hid c Hge).
  - destruct (op_current st c) as [j'|] eqn:Hcur; simpl.
    + pose proof (Hid c Hge) as Hnone0.
      rewrite Hcur in Hnone0.
      discriminate.
    + reflexivity.
  - destruct (op_current st c) as [j'|] eqn:Hcur; simpl.
    + pose proof (Hid c Hge) as Hnone0.
      rewrite Hcur in Hnone0.
      discriminate.
    + reflexivity.
  - exact (Hid c Hge).
  - exact (Hid c Hge).
  - exact (Hid c Hge).
  - destruct (Nat.eqb c c0) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c.
      exfalso.
      simpl in Hpre.
      lia.
    + exact (Hid c Hge).
  - destruct (Nat.eqb c c0) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c.
      exfalso.
      simpl in Hpre.
      lia.
    + exact (Hid c Hge).
  - exact (Hid c Hge).
  - exact (Hid c Hge).
Qed.

Lemma op_step_preserves_admissibility :
  forall adm m st ev st',
    op_respects_admissibility adm m st ->
    op_step_placement_pre adm m st ev ->
    op_step st ev st' ->
    op_respects_admissibility adm m st'.
Proof.
  intros adm m st ev st' Hadm Hpre Hstep c j Hlt Hcur.
  inversion Hstep; subst; clear Hstep; simpl in Hcur.
  - eapply Hadm; eauto.
  - destruct (op_current st c) as [j'|] eqn:Hc; try discriminate.
    destruct (Nat.eqb j' j0) eqn:Ej; try discriminate.
    inversion Hcur; subst. eapply Hadm; eauto.
  - destruct (op_current st c) as [j'|] eqn:Hc; try discriminate.
    destruct (Nat.eqb j' j0) eqn:Ej; try discriminate.
    inversion Hcur; subst. eapply Hadm; eauto.
  - eapply Hadm; eauto.
  - eapply Hadm; eauto.
  - eapply Hadm; eauto.
  - destruct Hpre as [Hdispatch_lt Hdispatch_adm].
    destruct (Nat.eqb c c0) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c.
      inversion Hcur; subst.
      exact Hdispatch_adm.
    + eapply Hadm; eauto.
  - destruct Hpre as [Hdispatch_lt Hdispatch_adm].
    destruct (Nat.eqb c c0) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c.
      inversion Hcur; subst.
      exact Hdispatch_adm.
    + eapply Hadm; eauto.
  - eapply Hadm; eauto.
  - eapply Hadm; eauto.
Qed.

Lemma op_step_preserves_multicore_projection_inv :
  forall adm m st ev st',
    op_multicore_projection_inv adm m st ->
    op_step_sound_pre st ev ->
    op_step_range_pre m ev ->
    op_step_placement_pre adm m st ev ->
    op_step st ev st' ->
    op_multicore_projection_inv adm m st'.
Proof.
  intros adm m st ev st' Hinv Hsound Hrange Hplace Hstep.
  destruct Hinv as [Hstruct Hidle Hadm].
  constructor.
  - eapply op_step_preserves_struct_inv; eauto.
  - eapply op_step_preserves_idle_outside_range; eauto.
  - eapply op_step_preserves_admissibility; eauto.
Qed.
