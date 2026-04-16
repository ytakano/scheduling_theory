From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Multicore.GlobalFairness.
From RocqSched Require Import Analysis.Multicore.GlobalAnalysisEntryPoints.
From RocqSched Require Import Examples.GlobalLLFExamples.
From RocqSched Require Import Examples.GlobalWorkConservingExamples.

Import ListNotations.

Section GlobalFairnessExamples.

  Example global_llf_excluded_job_contradicts_small_workload_upper_bound_example :
    total_job_cost llf_example_jobs [0; 2; 1] <= 2 * (2 - 1) -> False.
  Proof.
    intro Hbound.
    eapply (global_llf_not_running_eligible_job_interval_contradicts_workload_upper_bound
              llf_example_J llf_example_candidates
              llf_example_jobs 2 llf_example_sched 1 2 2 [0] [1]).
    - exact llf_example_candidates_spec.
    - exact llf_example_rel.
    - lia.
    - unfold llf_example_J. lia.
    - constructor; simpl; [intros [H | [H | []]]; discriminate|].
      constructor; simpl; [intros [H | []]; discriminate|].
      constructor; simpl; [intros []|constructor].
    - lia.
    - intros t Hrange.
      assert (t = 1) by lia.
      subst t.
      split.
      + unfold eligible, released, completed, llf_example_jobs, llf_job2.
        simpl.
        lia.
      + intros [cpu [Hlt Hrun]].
        destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate.
    - intros t Hrange c j Hc Hrun.
      assert (t = 1) by lia.
      subst t.
      destruct c as [|[|c']]; simpl in Hrun; try lia; inversion Hrun; subst; simpl; auto.
    - exact Hbound.
  Qed.

  Example global_edf_persistently_eligible_job_must_run_example :
    exists t, 0 <= t < 1 /\ running 2 example_sched 0 t.
  Proof.
    eapply (global_edf_persistently_eligible_job_must_run_in_interval
              example_J example_candidates
              example_jobs 2 example_sched 0 1 0 [] []).
    - exact example_candidates_spec.
    - exact example_edf_rel.
    - unfold example_J. reflexivity.
    - constructor; [simpl; tauto|constructor].
    - lia.
    - intros t Hrange.
      assert (t = 0) by lia.
      subst t.
      unfold eligible, released, completed, example_jobs, example_job.
      simpl.
      lia.
    - intros t Hrange Hnotrun c Hc j Hrun.
      assert (t = 0) by lia.
      subst t.
      destruct c as [|[|c']]; simpl in Hrun.
      + inversion Hrun; subst.
        exfalso.
        apply Hnotrun.
        exists 0.
        split; [lia|reflexivity].
      + discriminate.
      + lia.
    - simpl.
      lia.
  Qed.

End GlobalFairnessExamples.
