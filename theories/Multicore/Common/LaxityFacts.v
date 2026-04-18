From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.CompletionFacts.
From RocqSched Require Import Multicore.Common.RemainingCostFacts.

(** Public downstream theorems in this file:
    - exact running / not-running step lemmas for multicore laxity
    - step-bound lemmas for fairness and bounded-waiting clients *)

Lemma laxity_unfold_service_sum :
  forall jobs m sched j t,
    laxity jobs m sched j t =
      (Z.of_nat (job_abs_deadline (jobs j))
       - Z.of_nat t
       - Z.of_nat (job_cost (jobs j) - service_sum_on_cpus m sched j t))%Z.
Proof.
  intros jobs m sched j t.
  rewrite laxity_unfold.
  rewrite remaining_cost_eq_job_cost_minus_service_sum.
  reflexivity.
Qed.

Lemma laxity_step_running_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    running m sched j t ->
    ~ completed jobs m sched j t ->
    laxity jobs m sched j (S t) = laxity jobs m sched j t.
Proof.
  intros jobs m sched j t Hnd Hrun Hncomp.
  rewrite !laxity_unfold.
  pose proof (not_completed_implies_remaining_cost_pos jobs m sched j t Hncomp) as Hpos.
  rewrite (remaining_cost_step_running_mc jobs m sched j t Hnd Hrun Hncomp).
  rewrite Nat2Z.inj_sub by lia.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma laxity_step_not_running_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    ~ running m sched j t ->
    (laxity jobs m sched j (S t) = laxity jobs m sched j t - 1)%Z.
Proof.
  intros jobs m sched j t Hnd Hnrun.
  rewrite !laxity_unfold.
  rewrite (remaining_cost_step_not_running_mc jobs m sched j t Hnd Hnrun).
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma laxity_step_bounds_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    (laxity jobs m sched j t - 1 <= laxity jobs m sched j (S t))%Z /\
    (laxity jobs m sched j (S t) <= laxity jobs m sched j t)%Z.
Proof.
  intros jobs m sched j t Hnd.
  pose proof (remaining_cost_step_bounds_mc jobs m sched j t Hnd) as [Hdec Hstep].
  rewrite !laxity_unfold.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

Lemma laxity_interval_lower_bound :
  forall jobs m sched j t1 t2,
    no_duplication m sched ->
    t1 <= t2 ->
    (laxity jobs m sched j t1 - Z.of_nat (t2 - t1)
      <= laxity jobs m sched j t2)%Z.
Proof.
  intros jobs m sched j t1 t2 Hnd Hle.
  induction Hle as [|t2 Hle IH].
  - simpl. lia.
  - pose proof (laxity_step_bounds_mc jobs m sched j t2 Hnd) as [Hlb _].
    replace (Z.of_nat (S t2 - t1)) with (Z.of_nat (t2 - t1) + 1)%Z by lia.
    lia.
Qed.

Lemma laxity_interval_upper_bound :
  forall jobs m sched j t1 t2,
    valid_schedule jobs m sched ->
    no_duplication m sched ->
    t1 <= t2 ->
    (laxity jobs m sched j t2
      <= laxity jobs m sched j t1
         - Z.of_nat (t2 - t1)
         + Z.of_nat (service_between m sched j t1 t2))%Z.
Proof.
  intros jobs m sched j t1 t2 Hvalid Hnd Hle.
  pose proof (service_sum_on_cpus_monotone m sched j t1 t2 Hle) as Hmono.
  pose proof
    (valid_no_duplication_service_sum_le_cost jobs m sched j t1 Hvalid Hnd)
    as Hcost_t1.
  pose proof
    (valid_no_duplication_service_sum_le_cost jobs m sched j t2 Hvalid Hnd)
    as Hcost_t2.
  rewrite !laxity_unfold_service_sum.
  rewrite service_between_eq_sum_of_cpu_services.
  rewrite (Nat2Z.inj_sub
             (service_sum_on_cpus m sched j t2)
             (service_sum_on_cpus m sched j t1)) by lia.
  rewrite (Nat2Z.inj_sub
             (job_cost (jobs j))
             (service_sum_on_cpus m sched j t1)) by lia.
  rewrite (Nat2Z.inj_sub
             (job_cost (jobs j))
             (service_sum_on_cpus m sched j t2)) by lia.
  lia.
Qed.
