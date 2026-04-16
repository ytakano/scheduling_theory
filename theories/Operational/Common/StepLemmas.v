From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
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
  | EvWakeup j => ~ In j (op_runnable st) /\ ~ op_job_running st j
  | _ => True
  end.

Lemma add_runnable_preserves_struct_inv :
  forall m st j,
    op_struct_inv m st ->
    ~ In j (op_runnable st) ->
    ~ op_job_running st j ->
    op_struct_inv m (add_runnable j st).
Proof.
  intros m st j Hinv Hnotin Hnotrunning.
  destruct Hinv as [Hdup Hnodup Hsep].
  constructor.
  - exact Hdup.
  - simpl. constructor; assumption.
  - intros c j' Hlt Hcur.
    simpl.
    intros [Heq|Hin].
    + subst j'.
      apply Hnotrunning.
      exists c. exact Hcur.
    + eapply Hsep; eauto.
Qed.

Lemma clear_current_and_request_preserves_struct_inv :
  forall m st j,
    op_struct_inv m st ->
    op_struct_inv m (clear_current_and_request j st).
Proof.
  intros m st j Hinv.
  destruct Hinv as [Hdup Hnodup Hsep].
  constructor.
  - intros j' c1 c2 Hlt1 Hlt2.
    intros Hcur1 Hcur2.
    simpl in Hcur1, Hcur2.
    destruct (op_current st c1) as [k1|] eqn:Hc1; try discriminate.
    destruct (Nat.eqb k1 j) eqn:Ek1; try discriminate.
    destruct (op_current st c2) as [k2|] eqn:Hc2; try discriminate.
    destruct (Nat.eqb k2 j) eqn:Ek2; try discriminate.
    inversion Hcur1; inversion Hcur2; subst.
    eapply Hdup; eauto.
  - simpl. apply remove_job_preserves_NoDup. exact Hnodup.
  - intros c j' Hlt.
    intros Hcur Hin.
    simpl in Hcur.
    destruct (op_current st c) as [k|] eqn:Hc; try discriminate.
    destruct (Nat.eqb k j) eqn:Ek; try discriminate.
    inversion Hcur; subst.
    apply remove_job_in in Hin as [Hin' _].
    eapply Hsep; eauto.
Qed.

Lemma set_need_resched_preserves_struct_inv :
  forall m st c b,
    op_struct_inv m st ->
    op_struct_inv m (set_need_resched c b st).
Proof.
  intros m st c b [Hdup Hnodup Hsep].
  constructor; simpl; assumption.
Qed.

Lemma dispatch_target_not_in_remove_job :
  forall j xs,
    ~ In j (remove_job j xs).
Proof.
  apply remove_job_not_in.
Qed.

Lemma dispatch_other_not_in_remove_job :
  forall j j' xs,
    j' <> j ->
    ~ In j' xs ->
    ~ In j' (remove_job j xs).
Proof.
  intros j j' xs Hneq Hnotin Hin.
  apply remove_job_in in Hin as [Hin _].
  contradiction.
Qed.

Lemma dispatch_preserves_struct_inv :
  forall m st c j,
    op_struct_inv m st ->
    In j (op_runnable st) ->
    op_current st c = None ->
    c < m ->
    op_struct_inv
      m
      (clear_need_resched c
         (mkOpState
            (fun c' => if Nat.eqb c' c then Some j else op_current st c')
            (remove_job j (op_runnable st))
            (op_need_resched st))).
Proof.
  intros m st c j Hinv Hin Hjnone Hltc.
  destruct Hinv as [Hdup Hnodup Hsep].
  constructor.
  - intros j' c1 c2 Hlt1 Hlt2.
    simpl.
    destruct (Nat.eqb c1 c) eqn:Ec1, (Nat.eqb c2 c) eqn:Ec2;
      intros Hcur1 Hcur2.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_eq in Ec2.
      lia.
    + apply Nat.eqb_eq in Ec1.
      apply Nat.eqb_neq in Ec2.
      subst c1.
      inversion Hcur1; subst j'.
      exfalso.
      eapply (Hsep c2 j); eauto.
    + apply Nat.eqb_neq in Ec1.
      apply Nat.eqb_eq in Ec2.
      subst c2.
      inversion Hcur2; subst j'.
      exfalso.
      eapply (Hsep c1 j); eauto.
    + eapply Hdup; eauto.
  - simpl. apply remove_job_preserves_NoDup. exact Hnodup.
  - intros c' j' Hlt'.
    intros Hcur Hin'.
    simpl in Hcur.
    destruct (Nat.eqb c' c) eqn:Ecc.
    + apply Nat.eqb_eq in Ecc. subst c'.
      inversion Hcur; subst j'.
      exact (dispatch_target_not_in_remove_job j (op_runnable st) Hin').
    + apply Nat.eqb_neq in Ecc.
      eapply Hsep; eauto.
      eapply remove_job_in in Hin' as [Hin'' _].
      exact Hin''.
Qed.

Lemma op_step_preserves_struct_inv :
  forall m st ev st',
    op_struct_inv m st ->
    op_step_sound_pre st ev ->
    op_step st ev st' ->
    (forall c j, ev = EvDispatch c j -> c < m) ->
    op_struct_inv m st'.
Proof.
  intros m st ev st' Hinv Hpre Hstep Hdispatch_lt.
  inversion Hstep; subst; clear Hstep.
  - destruct Hpre as [Hnotin Hnotrunning].
    apply add_runnable_preserves_struct_inv; assumption.
  - apply clear_current_and_request_preserves_struct_inv; assumption.
  - apply clear_current_and_request_preserves_struct_inv; assumption.
  - apply set_need_resched_preserves_struct_inv; assumption.
  - eapply dispatch_preserves_struct_inv; eauto using Hdispatch_lt.
  - exact Hinv.
Qed.
