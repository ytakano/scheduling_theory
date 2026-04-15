From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Multicore.GlobalAnalysisEntryPoints.
From RocqSched Require Import Examples.GlobalServiceExamples.
From RocqSched Require Import Examples.GlobalLLFExamples.
Import ListNotations.

Section GlobalInterferenceExamples.

  Example global_llf_excluded_eligible_job_interval_implies_full_supply_example :
    total_cpu_service_between 2 llf_example_sched 1 2 = 2 * (2 - 1).
  Proof.
    eapply (global_llf_not_running_eligible_job_interval_implies_full_supply
              llf_example_J llf_example_candidates
              llf_example_jobs 2 llf_example_sched 1 2 2).
    - exact llf_example_candidates_spec.
    - exact llf_example_rel.
    - lia.
    - unfold llf_example_J. lia.
    - intros t Hrange.
      assert (t = 1) by lia.
      subst t.
      split.
      + unfold eligible, released, completed, llf_example_jobs, llf_job2.
        simpl.
        lia.
      + intros [cpu [Hlt Hrun]].
        destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate.
  Qed.

  Example global_covering_list_recovers_machine_supply_example :
    total_cpu_service_between 2 migrating_sched 0 2 =
    total_service_between_list 2 migrating_sched [0] 0 2.
  Proof.
    eapply total_service_between_list_covers_total_cpu_supply.
    - apply migrating_schedule_no_duplication.
    - constructor; simpl; [tauto|constructor].
    - lia.
    - intros t Hrange c j Hc Hrun.
      assert (t = 0 \/ t = 1) by lia.
      destruct H as [-> | ->];
        destruct c as [|[|c']]; simpl in Hrun; try discriminate; inversion Hrun; subst; simpl; auto.
  Qed.

  Example global_llf_excluded_job_interval_implies_workload_gap_example :
    2 * (2 - 1) < total_job_cost llf_example_jobs [0; 2; 1].
  Proof.
    eapply (global_llf_not_running_eligible_job_interval_implies_workload_gap
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
  Qed.

End GlobalInterferenceExamples.
