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

Lemma valid_no_duplication_service_sum_le_cost :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    no_duplication m sched ->
    service_sum_on_cpus m sched j t <= job_cost (jobs j).
Proof.
  intros jobs m sched j t Hvalid Hnd.
  induction t as [|t IH].
  - rewrite <- service_job_eq_sum_of_cpu_services.
    simpl.
    apply Nat.le_0_l.
  - rewrite service_sum_on_cpus_step.
    destruct (no_duplication_cpu_count_0_or_1 m sched j t Hnd) as [Hzero | Hone].
    + rewrite Hzero. lia.
    + assert (Hrun : running m sched j t).
      { apply (proj1 (no_duplication_cpu_count_eq_1_iff_executed m sched j t Hnd)).
        exact Hone.
      }
      pose proof (valid_running_implies_service_sum_lt_cost jobs m sched j t Hvalid Hrun)
        as Hlt.
      lia.
Qed.

Lemma valid_no_duplication_service_between_le_cost :
  forall jobs m sched j t1 t2,
    valid_schedule jobs m sched ->
    no_duplication m sched ->
    t1 <= t2 ->
    service_between m sched j t1 t2 <= job_cost (jobs j).
Proof.
  intros jobs m sched j t1 t2 Hvalid Hnd Hle.
  rewrite service_between_eq_sum_of_cpu_services by lia.
  pose proof (valid_no_duplication_service_sum_le_cost jobs m sched j t2 Hvalid Hnd)
    as Hbound.
  lia.
Qed.
