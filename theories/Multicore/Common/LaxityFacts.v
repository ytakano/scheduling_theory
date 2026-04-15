From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.RemainingCostFacts.

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
