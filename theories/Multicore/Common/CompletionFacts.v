From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.

Lemma completed_iff_service_sum_ge_cost :
  forall jobs m sched j t,
    completed jobs m sched j t <->
    job_cost (jobs j) <= service_sum_on_cpus m sched j t.
Proof.
  intros jobs m sched j t.
  rewrite completed_iff_service_ge_cost.
  rewrite service_job_eq_sum_of_cpu_services.
  tauto.
Qed.

Lemma not_completed_iff_service_sum_lt_cost :
  forall jobs m sched j t,
    ~ completed jobs m sched j t <->
    service_sum_on_cpus m sched j t < job_cost (jobs j).
Proof.
  intros jobs m sched j t.
  rewrite completed_iff_service_sum_ge_cost.
  lia.
Qed.

Lemma missed_deadline_iff_service_sum_lt_cost_at_deadline :
  forall jobs m sched j,
    missed_deadline jobs m sched j <->
    service_sum_on_cpus m sched j (job_abs_deadline (jobs j)) <
    job_cost (jobs j).
Proof.
  intros jobs m sched j.
  rewrite missed_deadline_iff_service_lt_cost_at_deadline.
  rewrite service_job_eq_sum_of_cpu_services.
  tauto.
Qed.

Lemma eligible_iff_released_and_service_sum_lt_cost :
  forall jobs m sched j t,
    eligible jobs m sched j t <->
    released jobs j t /\
    service_sum_on_cpus m sched j t < job_cost (jobs j).
Proof.
  intros jobs m sched j t.
  unfold eligible.
  rewrite not_completed_iff_service_sum_lt_cost.
  tauto.
Qed.

Lemma valid_running_implies_service_sum_lt_cost :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    running m sched j t ->
    service_sum_on_cpus m sched j t < job_cost (jobs j).
Proof.
  intros jobs m sched j t Hvalid [c [Hlt Hrun]].
  pose proof (valid_running_implies_eligible jobs m sched j t c Hvalid Hlt Hrun)
    as Helig.
  rewrite eligible_iff_released_and_service_sum_lt_cost in Helig.
  exact (proj2 Helig).
Qed.
