From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.CompletionFacts.

(** Public downstream theorems in this file:
    - exact running / not-running step lemmas for multicore remaining cost
    - step-bound and monotonicity lemmas for interval clients *)

Lemma remaining_cost_eq_job_cost_minus_service_sum :
  forall jobs m sched j t,
    remaining_cost jobs m sched j t =
    job_cost (jobs j) - service_sum_on_cpus m sched j t.
Proof.
  intros jobs m sched j t.
  unfold remaining_cost.
  rewrite service_job_eq_sum_of_cpu_services.
  reflexivity.
Qed.

Lemma remaining_cost_step_running_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    running m sched j t ->
    ~ completed jobs m sched j t ->
    remaining_cost jobs m sched j (S t) =
    remaining_cost jobs m sched j t - 1.
Proof.
  intros jobs m sched j t Hnd Hrun Hncomp.
  rewrite !remaining_cost_eq_job_cost_minus_service_sum.
  rewrite service_sum_on_cpus_step.
  rewrite (proj2 (no_duplication_cpu_count_eq_1_iff_executed m sched j t Hnd)).
  - pose proof (proj1 (not_completed_iff_service_sum_lt_cost jobs m sched j t) Hncomp)
      as Hlt.
    lia.
  - exact Hrun.
Qed.

Lemma remaining_cost_step_not_running_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    ~ running m sched j t ->
    remaining_cost jobs m sched j (S t) =
    remaining_cost jobs m sched j t.
Proof.
  intros jobs m sched j t Hnd Hnrun.
  rewrite !remaining_cost_eq_job_cost_minus_service_sum.
  rewrite service_sum_on_cpus_step.
  pose proof (no_duplication_cpu_count_0_or_1 m sched j t Hnd) as [Hzero | Hone].
  - lia.
  - exfalso.
    apply Hnrun.
    apply (proj1 (no_duplication_cpu_count_eq_1_iff_executed m sched j t Hnd)).
    exact Hone.
Qed.

Lemma remaining_cost_step_bounds_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    remaining_cost jobs m sched j (S t) <= remaining_cost jobs m sched j t /\
    remaining_cost jobs m sched j t <= S (remaining_cost jobs m sched j (S t)).
Proof.
  intros jobs m sched j t Hnd.
  rewrite !remaining_cost_eq_job_cost_minus_service_sum.
  rewrite service_sum_on_cpus_step.
  destruct (no_duplication_cpu_count_0_or_1 m sched j t Hnd) as [Hzero | Hone];
    rewrite ?Hzero, ?Hone; lia.
Qed.

Lemma remaining_cost_monotone_mc :
  forall jobs m sched j t1 t2,
    no_duplication m sched ->
    t1 <= t2 ->
    remaining_cost jobs m sched j t2 <= remaining_cost jobs m sched j t1.
Proof.
  intros jobs m sched j t1 t2 Hnd Hle.
  induction Hle as [|t2 Hle IH].
  - lia.
  - pose proof (remaining_cost_step_bounds_mc jobs m sched j t2 Hnd) as [Hstep _].
    lia.
Qed.
