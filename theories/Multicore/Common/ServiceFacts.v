From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.

(** Public downstream theorems in this file:
    - migration-aware service decomposition via
      `service_job_eq_sum_of_cpu_services` and
      `service_between_eq_sum_of_cpu_services`
    - machine supply definitions and semantic step/interval bounds
    - bridges from `machine_full_at` to machine supply saturation *)

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

(* Migration-aware cumulative service on an m-CPU schedule, decomposed into
   the sum of the per-CPU 1-CPU schedule projections. *)
Fixpoint service_sum_on_cpus
    (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      service_job 1 (cpu_schedule sched m') j t +
      service_sum_on_cpus m' sched j t
  end.

Fixpoint cpu_count_sum_on_cpus
    (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      cpu_count 1 (cpu_schedule sched m') j t +
      cpu_count_sum_on_cpus m' sched j t
  end.

Lemma cpu_count_1_cpu_schedule_eq_runs_on :
  forall sched c j t,
    cpu_count 1 (cpu_schedule sched c) j t =
    if runs_on sched j t c then 1 else 0.
Proof.
  intros sched c j t.
  simpl.
  rewrite runs_on_cpu_schedule.
  destruct (runs_on sched j t c); lia.
Qed.

Lemma cpu_count_eq_sum_of_cpu_counts :
  forall m sched j t,
    cpu_count m sched j t = cpu_count_sum_on_cpus m sched j t.
Proof.
  induction m as [|m' IH]; intros sched j t.
  - reflexivity.
  - simpl.
    rewrite runs_on_cpu_schedule.
    rewrite IH.
    lia.
Qed.

Lemma cpu_count_eq_sum_of_local_cpu_counts :
  forall m sched j t,
    cpu_count m sched j t = cpu_count_sum_on_cpus m sched j t.
Proof.
  exact cpu_count_eq_sum_of_cpu_counts.
Qed.

Lemma service_sum_on_cpus_step :
  forall m sched j t,
    service_sum_on_cpus m sched j (S t) =
    service_sum_on_cpus m sched j t + cpu_count m sched j t.
Proof.
  induction m as [|m' IH]; intros sched j t.
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite runs_on_cpu_schedule.
    lia.
Qed.

Lemma service_job_eq_sum_of_cpu_services :
  forall m sched j t,
    service_job m sched j t = service_sum_on_cpus m sched j t.
Proof.
  intros m sched j t.
  induction t as [|t' IH].
  - induction m as [|m' IHm].
    + reflexivity.
    + simpl.
      simpl in IHm.
      rewrite <- IHm.
      lia.
  - rewrite service_job_step.
    rewrite service_sum_on_cpus_step.
    rewrite IH.
    lia.
Qed.

Lemma service_sum_on_cpus_monotone :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_sum_on_cpus m sched j t1 <= service_sum_on_cpus m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  induction Hle.
  - lia.
  - rewrite service_sum_on_cpus_step.
    lia.
Qed.

Lemma service_between_eq_sum_of_cpu_services :
  forall m sched j t1 t2,
    service_between m sched j t1 t2 =
    service_sum_on_cpus m sched j t2 -
    service_sum_on_cpus m sched j t1.
Proof.
  intros m sched j t1 t2.
  unfold service_between.
  repeat rewrite <- service_job_eq_sum_of_cpu_services.
  reflexivity.
Qed.

Lemma no_duplication_cpu_count_sum_le_1 :
  forall m sched j t,
    no_duplication m sched ->
    cpu_count_sum_on_cpus m sched j t <= 1.
Proof.
  intros m sched j t Hnd.
  rewrite <- cpu_count_eq_sum_of_local_cpu_counts.
  apply no_duplication_cpu_count_le_1.
  exact Hnd.
Qed.

Lemma no_duplication_service_sum_step_le_1 :
  forall m sched j t,
    no_duplication m sched ->
    service_sum_on_cpus m sched j (S t) <=
    service_sum_on_cpus m sched j t + 1.
Proof.
  intros m sched j t Hnd.
  rewrite service_sum_on_cpus_step.
  pose proof (no_duplication_cpu_count_le_1 m sched j t Hnd) as Hle.
  lia.
Qed.

Lemma machine_full_at_implies_total_cpu_service_at_eq_m :
  forall m sched t,
    machine_full_at m sched t ->
    total_cpu_service_at m sched t = m.
Proof.
  induction m as [|m IH]; intros sched t Hfull.
  - reflexivity.
  - simpl.
    assert (Htail : machine_full_at m sched t).
    { intros c Hc.
      apply Hfull.
      lia.
    }
    pose proof (Hfull m ltac:(lia)) as [j Hj].
    rewrite Hj.
    rewrite IH by exact Htail.
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
    assert (Hslot : total_cpu_service_at m sched t1 = m).
    { apply total_cpu_service_at_eq_num_cpus_if_all_cpus_busy.
      intros c Hc.
      specialize (Hbusy t1 ltac:(lia)).
      exact (Hbusy c Hc).
    }
    destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
    + rewrite total_cpu_service_between_single_slot.
      rewrite Hslot.
      assert (S len = 1) by lia.
      lia.
    + assert (Hlen' : len = t2 - S t1) by lia.
      assert (Hbusy_rest :
        forall t, S t1 <= t < t2 -> forall c, c < m -> cpu_busy sched t c).
      { intros t Hrange c Hc.
        specialize (Hbusy t ltac:(lia)).
        exact (Hbusy c Hc).
      }
      assert (Hrest :
        total_cpu_service_between m sched (S t1) t2 = m * len).
      { apply IH; assumption. }
      rewrite (total_cpu_service_between_split m sched t1 (S t1) t2) by lia.
      rewrite total_cpu_service_between_single_slot.
      rewrite Hslot, Hrest, Hlen'.
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

Lemma service_between_single_slot_eq_cpu_count :
  forall m sched j t,
    service_between m sched j t (S t) = cpu_count m sched j t.
Proof.
  intros m sched j t.
  unfold service_between.
  rewrite service_job_step.
  lia.
Qed.

Lemma cpu_count_le_total_cpu_service_at :
  forall m sched j t,
    cpu_count m sched j t <= total_cpu_service_at m sched t.
Proof.
  induction m as [|m IH]; intros sched j t.
  - reflexivity.
  - simpl.
    pose proof (IH sched j t) as Hrest.
    destruct (runs_on sched j t m) eqn:Hruns;
      destruct (sched t m) eqn:Hsched; simpl in *.
    + lia.
    + apply runs_on_true_iff in Hruns.
      rewrite Hsched in Hruns.
      discriminate.
    + lia.
    + lia.
Qed.

Lemma service_between_le_total_cpu_service_between :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_between m sched j t1 t2 <=
    total_cpu_service_between m sched t1 t2.
Proof.
  intros m sched j t1 t2 Hle.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen.
  induction len as [|len IH]; intros t1 t2 Hle Hlen.
  - assert (t1 = t2) by lia.
    subst t2.
    rewrite service_between_refl.
    rewrite total_cpu_service_between_refl.
    lia.
  - destruct (Nat.eq_dec t2 t1) as [-> | Hneq].
    + lia.
    + destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
      * rewrite service_between_single_slot_eq_cpu_count.
        rewrite total_cpu_service_between_single_slot.
        apply cpu_count_le_total_cpu_service_at.
      * assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (service_between_split m sched j t1 (S t1) t2) by lia.
        rewrite (total_cpu_service_between_split m sched t1 (S t1) t2) by lia.
        rewrite service_between_single_slot_eq_cpu_count.
        rewrite total_cpu_service_between_single_slot.
        assert (Hslot : cpu_count m sched j t1 <= total_cpu_service_at m sched t1).
        { apply cpu_count_le_total_cpu_service_at. }
        pose proof (IH (S t1) t2 ltac:(lia) Hlen') as Hrest.
        lia.
Qed.

Lemma persistently_not_running_implies_service_between_zero :
  forall m sched j t1 t2,
    t1 <= t2 ->
    (forall t, t1 <= t < t2 -> ~ running m sched j t) ->
    service_between m sched j t1 t2 = 0.
Proof.
  intros m sched j t1 t2 Hle Hnotrun.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen Hnotrun.
  induction len as [|len IH]; intros t1 t2 Hle Hlen Hnotrun.
  - assert (t1 = t2) by lia.
    subst t2.
    apply service_between_refl.
  - assert (Ht1t2 : t1 < t2) by lia.
    destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq].
    + rewrite service_between_single_slot_eq_cpu_count.
      destruct (Nat.eq_dec (cpu_count m sched j t1) 0) as [Hzero | Hnz].
      * exact Hzero.
      * exfalso.
        apply (Hnotrun t1 ltac:(lia)).
        apply cpu_count_nonzero_iff_executed.
        exact Hnz.
    + assert (Hlen' : len = t2 - S t1) by lia.
      rewrite (service_between_split m sched j t1 (S t1) t2) by lia.
      rewrite service_between_single_slot_eq_cpu_count.
      assert (Hzero : cpu_count m sched j t1 = 0).
      { destruct (Nat.eq_dec (cpu_count m sched j t1) 0) as [Hz | Hnz].
        - exact Hz.
        - exfalso.
          apply (Hnotrun t1 ltac:(lia)).
          apply cpu_count_nonzero_iff_executed.
          exact Hnz.
      }
      rewrite Hzero.
      rewrite (IH (S t1) t2).
      * lia.
      * lia.
      * exact Hlen'.
      * intros t Hrange.
        apply Hnotrun.
        lia.
Qed.

Lemma no_duplication_service_between_le_interval_length :
  forall m sched j t1 t2,
    no_duplication m sched ->
    t1 <= t2 ->
    service_between m sched j t1 t2 <= t2 - t1.
Proof.
  intros m sched j t1 t2 Hnd Hle.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle Hlen.
  induction len as [|len IH]; intros t1 t2 Hle Hlen.
  - assert (t1 = t2) by lia.
    subst t2.
    rewrite service_between_refl.
    lia.
  - destruct (Nat.eq_dec t2 t1) as [-> | Hneq].
    + lia.
    + destruct (Nat.eq_dec t2 (S t1)) as [-> | Hneq'].
      * rewrite service_between_single_slot_eq_cpu_count.
        pose proof (no_duplication_cpu_count_le_1 m sched j t1 Hnd) as Hcpu.
        lia.
      * assert (Hlen' : len = t2 - S t1) by lia.
        rewrite (service_between_split m sched j t1 (S t1) t2) by lia.
        rewrite service_between_single_slot_eq_cpu_count.
        pose proof (no_duplication_cpu_count_le_1 m sched j t1 Hnd) as Hcpu.
        pose proof (IH (S t1) t2 ltac:(lia) Hlen') as Hrest.
        lia.
Qed.
