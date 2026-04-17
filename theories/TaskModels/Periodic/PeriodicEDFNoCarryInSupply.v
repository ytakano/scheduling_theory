From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Definition periodic_edf_backlog_free_before_release
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (sched : Schedule)
    (j : JobId) : Prop :=
  forall t1 t2 x,
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_release (jobs j) ->
    periodic_jobset_deadline_between
      T tasks offset jobs t1 (job_abs_deadline (jobs j)) x ->
    job_release (jobs x) < job_release (jobs j) ->
    completed jobs 1 sched x (job_release (jobs j)).

Lemma periodic_edf_no_carry_in_bridge_of_backlog_free :
  forall T tasks offset jobs H sched j,
    valid_schedule jobs 1 sched ->
    periodic_edf_backlog_free_before_release
      T tasks offset jobs H sched j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs H sched j.
Proof.
  intros T tasks offset jobs H sched j Hvalid Hbacklog.
  constructor.
  intros t1 t2 Hwit Ht1rel t j_run Hbetween Hsched Hdeadline_between.
  destruct (Nat.le_gt_cases
              (job_release (jobs j))
              (job_release (jobs j_run))) as [Hle | Hlt].
  - exact Hle.
  - exfalso.
    destruct Hbetween as [Hrel_t _].
    assert (Hcompleted_at_release :
      completed jobs 1 sched j_run (job_release (jobs j))).
    {
      eapply Hbacklog; eauto.
    }
    assert (Hcompleted_at_t :
      completed jobs 1 sched j_run t).
    {
      eapply completed_monotone; eauto.
    }
    pose proof
      (valid_no_run_after_completion
         jobs 1 sched j_run t 0 Hvalid ltac:(lia) Hsched)
      as Hnot_completed.
    exact (Hnot_completed Hcompleted_at_t).
Qed.
