From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.TopMMetricChooser.
From RocqSched Require Import Uniprocessor.Policies.Common.MetricChooser.
From RocqSched Require Import Multicore.Global.GlobalEDF.
Import ListNotations.

Section GlobalEDFWorkConservingExample.

  Definition example_job : Job := mkJob 0 0 0 1 2.

  Definition example_jobs (_ : JobId) : Job := example_job.

  Definition example_J (j : JobId) : Prop := j = 0.

  Definition example_candidates : CandidateSource :=
    fun _jobs _m _sched _t => [0].

  Definition example_sched (t : Time) (cpu : CPU) : option JobId :=
    if Nat.eqb cpu 0 then
      if Nat.eqb t 0 then Some 0 else None
    else None.

  Lemma example_candidates_spec :
    CandidateSourceSpec example_J example_candidates.
  Proof.
    refine (mkCandidateSourceSpec example_J example_candidates _ _ _).
    - intros jobs m sched t j Hin.
      simpl in Hin.
      destruct Hin as [Hj | []].
      symmetry.
      exact Hj.
    - intros jobs m sched t j Hj _.
      unfold example_J in Hj.
      subst j.
      simpl.
      left.
      reflexivity.
    - intros jobs m s1 s2 t _.
      reflexivity.
  Qed.

  Lemma example_service_positive :
    forall t,
      1 <= t ->
      1 <= service_job 2 example_sched 0 t.
  Proof.
    induction t as [|t' IH].
    - lia.
    - intros Hle.
      destruct t' as [|t''].
      + simpl.
        unfold runs_on, example_sched.
        simpl.
        lia.
      + rewrite service_job_step.
        assert (1 <= service_job 2 example_sched 0 (S t'')) by (apply IH; lia).
        lia.
  Qed.

  Lemma example_job_not_eligible_after_start :
    forall t,
      1 <= t ->
      ~ eligible example_jobs 2 example_sched 0 t.
  Proof.
    intros t Hle [Hrel Hncomp].
    apply Hncomp.
    rewrite completed_iff_service_ge_cost.
    unfold example_jobs, example_job.
    simpl.
    exact (example_service_positive t Hle).
  Qed.

  Lemma example_edf_rel :
    scheduler_rel (global_edf_scheduler example_candidates) example_jobs 2 example_sched.
  Proof.
    unfold global_edf_scheduler, top_m_algorithm_schedule.
    intros t c.
    destruct c as [|[|c']].
    - destruct t as [|t'].
      + reflexivity.
      + unfold example_sched.
        simpl.
        change
          (None =
           nth_error
             (choose_top_m_by_metric 2
                (global_edf_metric_of_jobs example_jobs)
                example_jobs 2 example_sched (S t') [0]) 0).
        simpl.
        rewrite (choose_min_metric_none_if_no_eligible
                   (global_edf_metric_of_jobs example_jobs)
                   example_jobs 2 example_sched (S t') [0]).
        reflexivity.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply example_job_not_eligible_after_start.
        lia.
    - destruct t as [|t'].
      + change
          (None =
           nth_error
             (choose_top_m_by_metric 2
                (global_edf_metric_of_jobs example_jobs)
                example_jobs 2 example_sched 0 [0]) 1).
        simpl.
        reflexivity.
      + change
          (None =
           nth_error
             (choose_top_m_by_metric 2
                (global_edf_metric_of_jobs example_jobs)
                example_jobs 2 example_sched (S t') [0]) 1).
        simpl.
        rewrite (choose_min_metric_none_if_no_eligible
                   (global_edf_metric_of_jobs example_jobs)
                   example_jobs 2 example_sched (S t') [0]).
        reflexivity.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply example_job_not_eligible_after_start.
        lia.
    - unfold example_sched.
      simpl.
      reflexivity.
  Qed.

  Example global_edf_running_from_admissible_somewhere_example :
    running 2 example_sched 0 0.
  Proof.
    apply (global_edf_running_if_some_cpu_idle_and_subset_admissible_somewhere
             example_J example_candidates example_jobs 2 example_sched 0 0).
    - exact example_candidates_spec.
    - exact example_edf_rel.
    - lia.
    - exists 1. split; [lia | reflexivity].
    - unfold example_J. reflexivity.
    - exists 0.
      unfold eligible_on_cpu, runnable_on_cpu.
      split; [lia |].
      split; [exact I |].
      unfold eligible, released, completed, example_jobs, example_job.
      simpl.
      lia.
  Qed.

End GlobalEDFWorkConservingExample.
