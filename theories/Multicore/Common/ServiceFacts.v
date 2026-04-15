From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Multicore.ProcessorSupply.
From RocqSched Require Import Multicore.Common.MultiCoreBase.

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
