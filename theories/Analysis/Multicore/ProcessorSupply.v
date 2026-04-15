From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.

(** Public downstream theorems in this file:
    `total_cpu_service_between_eq_capacity_if_all_cpus_busy` and
    `total_cpu_service_between_le_capacity`.
    The remaining lemmas are primarily structural helpers for supply proofs. *)

(* CPU-level service contributed by all CPUs at time t. *)
Fixpoint total_cpu_service_at
    (m : nat) (sched : Schedule) (t : Time) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      (match sched t m' with
       | Some _ => 1
       | None => 0
       end) + total_cpu_service_at m' sched t
  end.

(* Cumulative machine supply in [0, t). *)
Fixpoint cumulative_total_cpu_service
    (m : nat) (sched : Schedule) (t : Time) : nat :=
  match t with
  | 0 => 0
  | S t' => total_cpu_service_at m sched t' + cumulative_total_cpu_service m sched t'
  end.

(* Machine supply in [t1, t2). *)
Definition total_cpu_service_between
    (m : nat) (sched : Schedule) (t1 t2 : Time) : nat :=
  cumulative_total_cpu_service m sched t2 -
  cumulative_total_cpu_service m sched t1.

Lemma total_cpu_service_at_le_num_cpus :
  forall m sched t,
    total_cpu_service_at m sched t <= m.
Proof.
  induction m as [|m IH]; intros sched t.
  - reflexivity.
  - simpl.
    pose proof (IH sched t) as Hrest.
    destruct (sched t m); simpl; lia.
Qed.

Lemma cumulative_total_cpu_service_step :
  forall m sched t,
    cumulative_total_cpu_service m sched (S t) =
    cumulative_total_cpu_service m sched t +
    total_cpu_service_at m sched t.
Proof.
  intros m sched t.
  simpl.
  lia.
Qed.

Lemma cumulative_total_cpu_service_monotone :
  forall m sched t1 t2,
    t1 <= t2 ->
    cumulative_total_cpu_service m sched t1 <=
    cumulative_total_cpu_service m sched t2.
Proof.
  intros m sched t1 t2 Hle.
  induction Hle.
  - lia.
  - rewrite cumulative_total_cpu_service_step.
    lia.
Qed.

Lemma total_cpu_service_between_eq :
  forall m sched t1 t2,
    total_cpu_service_between m sched t1 t2 =
    cumulative_total_cpu_service m sched t2 -
    cumulative_total_cpu_service m sched t1.
Proof.
  reflexivity.
Qed.

Lemma total_cpu_service_between_refl :
  forall m sched t,
    total_cpu_service_between m sched t t = 0.
Proof.
  intros m sched t.
  unfold total_cpu_service_between.
  lia.
Qed.

Lemma total_cpu_service_between_split :
  forall m sched t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    total_cpu_service_between m sched t1 t3 =
    total_cpu_service_between m sched t1 t2 +
    total_cpu_service_between m sched t2 t3.
Proof.
  intros m sched t1 t2 t3 H12 H23.
  unfold total_cpu_service_between.
  pose proof (cumulative_total_cpu_service_monotone m sched t1 t2 H12) as Hmon12.
  pose proof (cumulative_total_cpu_service_monotone m sched t2 t3 H23) as Hmon23.
  pose proof (cumulative_total_cpu_service_monotone m sched t1 t3 ltac:(lia)) as Hmon13.
  repeat rewrite Nat2Z.inj_sub by assumption.
  lia.
Qed.

Lemma total_cpu_service_between_single_slot :
  forall m sched t,
    total_cpu_service_between m sched t (S t) =
    total_cpu_service_at m sched t.
Proof.
  intros m sched t.
  unfold total_cpu_service_between.
  rewrite cumulative_total_cpu_service_step.
  lia.
Qed.

Lemma total_cpu_service_at_eq_num_cpus_if_all_cpus_busy :
  forall m sched t,
    (forall c, c < m -> cpu_busy sched t c) ->
    total_cpu_service_at m sched t = m.
Proof.
  induction m as [|m IH]; intros sched t Hbusy.
  - reflexivity.
  - simpl.
    assert (Hbusy_tail : forall c, c < m -> cpu_busy sched t c).
    { intros c Hc. apply Hbusy. lia. }
    pose proof (Hbusy m ltac:(lia)) as [j Hj].
    rewrite Hj.
    rewrite IH by exact Hbusy_tail.
    lia.
Qed.

Lemma total_cpu_service_between_eq_capacity_if_all_cpus_busy :
  forall m sched t1 t2,
    (forall t, t1 <= t < t2 -> forall c, c < m -> cpu_busy sched t c) ->
    total_cpu_service_between m sched t1 t2 = m * (t2 - t1).
Proof.
  intros m sched t1 t2 Hbusy.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hlen Hbusy.
  induction len as [|len IH]; intros t1 t2 Hlen Hbusy.
  - assert (t2 <= t1) by lia.
    pose proof (cumulative_total_cpu_service_monotone m sched t2 t1 H) as Hmon.
    unfold total_cpu_service_between.
    lia.
  - assert (Ht1t2 : t1 < t2) by lia.
    assert (Hslot :
      total_cpu_service_at m sched t1 = m)
      by (apply total_cpu_service_at_eq_num_cpus_if_all_cpus_busy;
          intros c Hc; apply (Hbusy t1); lia).
    destruct (Nat.eq_dec t2 (S t1)) as [->|Hneq'].
    + rewrite total_cpu_service_between_single_slot.
      rewrite Hslot.
      assert (S len = 1) by lia.
      lia.
    + assert (Hlen' : len = t2 - S t1) by lia.
      assert (Hbusy_rest :
        forall t, S t1 <= t < t2 -> forall c, c < m -> cpu_busy sched t c)
        by (intros t Hrange c Hc; apply (Hbusy t); lia).
      assert (Hrest :
        total_cpu_service_between m sched (S t1) t2 = m * len)
        by (apply IH; assumption).
      rewrite (total_cpu_service_between_split m sched t1 (S t1) t2) by lia.
      rewrite total_cpu_service_between_single_slot.
      rewrite Hslot, Hrest.
      rewrite Hlen'.
      lia.
Qed.

Lemma total_cpu_service_between_le_capacity :
  forall m sched t1 t2,
    total_cpu_service_between m sched t1 t2 <= m * (t2 - t1).
Proof.
  intros m sched t1 t2.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hlen.
  induction len as [|len IH]; intros t1 t2 Hlen.
  - assert (Hle' : t2 <= t1).
    { destruct (Nat.le_gt_cases t2 t1) as [Hle' | Hgt]; [exact Hle' |].
      exfalso.
      assert (0 < t2 - t1) by lia.
      rewrite Hlen in H.
      lia.
    }
    unfold total_cpu_service_between.
    pose proof (cumulative_total_cpu_service_monotone m sched t2 t1 Hle') as Hmon.
    lia.
  - destruct (Nat.eq_dec t2 t1) as [-> | Hneq].
    + lia.
    + destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
      * rewrite total_cpu_service_between_single_slot.
        pose proof (total_cpu_service_at_le_num_cpus m sched t1) as Hslot.
        assert (S len = 1) by lia.
        lia.
      * assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (total_cpu_service_between_split m sched t1 (S t1) t2) by lia.
        rewrite total_cpu_service_between_single_slot.
        pose proof (total_cpu_service_at_le_num_cpus m sched t1) as Hslot.
        pose proof (IH (S t1) t2 Hlen') as Hrest.
        lia.
Qed.
