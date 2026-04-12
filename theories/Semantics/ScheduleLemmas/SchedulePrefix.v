From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleFacts.
Import ListNotations.

(* ===== Section 1: Prefix agreement ===== *)

(* 2 つのスケジュールが時刻 t より前のすべての時点・CPU で一致する *)
Definition agrees_before (s1 s2 : Schedule) (t : Time) : Prop :=
  forall t' c, t' < t -> s1 t' c = s2 t' c.

(* 2-0: agrees_before は単調: t1 <= t2 かつ agrees t2 ならば agrees t1 *)
Lemma agrees_before_weaken :
  forall s1 s2 t1 t2,
    t1 <= t2 ->
    agrees_before s1 s2 t2 ->
    agrees_before s1 s2 t1.
Proof.
  intros s1 s2 t1 t2 Hle Hagree t' c Hlt.
  apply Hagree. lia.
Qed.

(* 2-1a: 反射律 *)
Lemma agrees_before_refl :
  forall s t, agrees_before s s t.
Proof.
  intros s t t' c _. reflexivity.
Qed.

(* 2-1b: 対称律 *)
Lemma agrees_before_sym :
  forall s1 s2 t, agrees_before s1 s2 t -> agrees_before s2 s1 t.
Proof.
  intros s1 s2 t Hagree t' c Hlt.
  symmetry. apply Hagree. exact Hlt.
Qed.

(* 2-1c: 推移律 *)
Lemma agrees_before_trans :
  forall s1 s2 s3 t,
    agrees_before s1 s2 t ->
    agrees_before s2 s3 t ->
    agrees_before s1 s3 t.
Proof.
  intros s1 s2 s3 t H12 H23 t' c Hlt.
  rewrite (H12 t' c Hlt). apply H23. exact Hlt.
Qed.

(* 2-2a (helper): 時刻 t での全 CPU が一致すれば cpu_count も一致 *)
Lemma cpu_count_agrees_at :
  forall m s1 s2 j t,
    (forall c, s1 t c = s2 t c) ->
    cpu_count m s1 j t = cpu_count m s2 j t.
Proof.
  induction m as [| m' IH]; intros s1 s2 j t Heq.
  - simpl. reflexivity.
  - simpl.
    unfold runs_on.
    rewrite (Heq m').
    rewrite (IH s1 s2 j t Heq).
    reflexivity.
Qed.

(* 2-2b: agrees_before s1 s2 t ならば service_job も一致 *)
Lemma agrees_before_service_job :
  forall m s1 s2 j t,
    agrees_before s1 s2 t ->
    service_job m s1 j t = service_job m s2 j t.
Proof.
  intros m s1 s2 j t Hagree.
  induction t as [| t' IH].
  - simpl. reflexivity.
  - rewrite (service_job_step m s1 j t').
    rewrite (service_job_step m s2 j t').
    assert (Hcpu : cpu_count m s1 j t' = cpu_count m s2 j t').
    { apply cpu_count_agrees_at.
      intro c. apply Hagree. lia. }
    assert (Hpre : agrees_before s1 s2 t').
    { apply (agrees_before_weaken s1 s2 t' (S t')). lia. exact Hagree. }
    rewrite (IH Hpre). rewrite Hcpu. reflexivity.
Qed.

(* 2-2c: completed の prefix extensionality *)
Lemma agrees_before_completed :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    completed jobs m s1 j t <-> completed jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold completed.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  tauto.
Qed.

(* 2-2d: eligible の prefix extensionality *)
Lemma agrees_before_eligible :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligible jobs m s1 j t <-> eligible jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligible.
  pose proof (agrees_before_completed jobs m s1 s2 j t Hagree) as Hcomp.
  tauto.
Qed.

(* 2-2e: ready の prefix extensionality
   注意: running は s t c を直接参照するため、agrees_before s1 s2 (S t) が必要
   (agrees_before s1 s2 t は strictly before t のみ保証するため不十分) *)
Lemma agrees_before_ready :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 (S t) ->
    ready jobs m s1 j t <-> ready jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  assert (Hpre : agrees_before s1 s2 t)
    by (apply (agrees_before_weaken s1 s2 t (S t)); [lia | exact Hagree]).
  pose proof (agrees_before_eligible jobs m s1 s2 j t Hpre) as Helig.
  assert (Hat : forall c, s1 t c = s2 t c)
    by (intro c; apply Hagree; lia).
  unfold ready.
  split.
  - intros [Hel Hnrun].
    split.
    + exact (proj1 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite (Hat c). exact Hrun.
  - intros [Hel Hnrun].
    split.
    + exact (proj2 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite <- (Hat c). exact Hrun.
Qed.

(* ===== Section 2: Boolean eligibility agrees with prefix ===== *)

(* Helper: eligibleb は service_job 経由のみ schedule を参照するため prefix 安定 *)
Lemma eligibleb_agrees_before :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligibleb jobs m s1 j t = eligibleb jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligibleb.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  reflexivity.
Qed.


(* remaining_cost is prefix-extensional because it only depends on service_job
   up to time t. *)
Lemma agrees_before_remaining_cost :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    remaining_cost jobs m s1 j t = remaining_cost jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold remaining_cost.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  reflexivity.
Qed.

(* laxity is prefix-extensional for the same reason. *)
Lemma agrees_before_laxity :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    laxity jobs m s1 j t = laxity jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold laxity.
  rewrite (agrees_before_remaining_cost jobs m s1 s2 j t Hagree).
  reflexivity.
Qed.
