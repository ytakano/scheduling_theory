From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
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
