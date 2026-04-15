From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.

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
