From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Policies.LLFOptimality.

Import ListNotations.

Lemma missed_deadline_implies_negative_laxity_at_deadline :
  forall jobs sched j,
    missed_deadline jobs 1 sched j ->
    (laxity jobs 1 sched j (job_abs_deadline (jobs j)) < 0)%Z.
Proof.
  intros jobs sched j Hmiss.
  rewrite laxity_unfold.
  apply (proj1 (missed_deadline_iff_service_lt_cost_at_deadline jobs 1 sched j)) in Hmiss.
  unfold remaining_cost.
  lia.
Qed.

Lemma nonnegative_laxity_at_deadline_implies_no_deadline_miss :
  forall jobs sched j,
    (0 <= laxity jobs 1 sched j (job_abs_deadline (jobs j)))%Z ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros jobs sched j Hlax Hmiss.
  pose proof (missed_deadline_implies_negative_laxity_at_deadline jobs sched j Hmiss).
  lia.
Qed.

Theorem llf_schedulable_by_on_of_feasible_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (llf_scheduler (enum_candidates_of enumJ)) jobs 1.
Proof.
  intros J J_bool enumJ jobs HJbool Hcomplete Hsound Hfeas.
  eapply llf_optimality_on_finite_jobs; eauto.
  apply enum_candidates_spec; assumption.
Qed.
