From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.
From RocqSched Require Import Multicore.Common.TopMMetricChooser.
From RocqSched Require Import Multicore.Global.GlobalLLF.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Common.MetricChooser.
Import ListNotations.

Section GlobalLLFExamples.

  Definition llf_job0 : Job := mkJob 0 0 1 1 2.
  Definition llf_job1 : Job := mkJob 0 1 1 1 3.
  Definition llf_job2 : Job := mkJob 0 2 1 1 5.

  Definition llf_example_jobs (j : JobId) : Job :=
    match j with
    | 0 => llf_job0
    | 1 => llf_job1
    | _ => llf_job2
    end.

  Definition llf_example_J (j : JobId) : Prop := j < 3.

  Definition llf_example_candidates : CandidateSource :=
    fun _jobs _m _sched _t => [0; 1; 2].

  Definition llf_example_sched (t : Time) (cpu : CPU) : option JobId :=
    match t, cpu with
    | 1, 0 => Some 0
    | 1, 1 => Some 1
    | 2, 0 => Some 2
    | _, _ => None
    end.

  Lemma llf_example_candidates_spec :
    CandidateSourceSpec llf_example_J llf_example_candidates.
  Proof.
    refine (mkCandidateSourceSpec llf_example_J llf_example_candidates _ _ _).
    - intros jobs m sched t j Hin.
      simpl in Hin.
      destruct Hin as [Hj | [Hj | [Hj | []]]];
        subst; unfold llf_example_J; lia.
    - intros jobs m sched t j Hj _.
      unfold llf_example_candidates.
      simpl.
      unfold llf_example_J in Hj.
      destruct j as [|[|[|j']]]; try lia; auto.
    - intros jobs m s1 s2 t _.
      reflexivity.
  Qed.

  Lemma llf_example_not_eligible_at_0 :
    forall j,
      In j [0; 1; 2] ->
      ~ eligible llf_example_jobs 2 llf_example_sched j 0.
  Proof.
    intros j Hin [Hrel _].
    destruct Hin as [Hj | [Hj | [Hj | []]]]; subst j;
      unfold eligible, released, llf_example_jobs, llf_job0, llf_job1, llf_job2 in Hrel;
      simpl in Hrel; lia.
  Qed.

  Lemma llf_example_service_at_3 :
    service_job 2 llf_example_sched 0 3 = 1 /\
    service_job 2 llf_example_sched 1 3 = 1 /\
    service_job 2 llf_example_sched 2 3 = 1.
  Proof.
    simpl.
    repeat split; reflexivity.
  Qed.

  Lemma llf_example_not_eligible_after_3 :
    forall t j,
      3 <= t ->
      In j [0; 1; 2] ->
      ~ eligible llf_example_jobs 2 llf_example_sched j t.
  Proof.
    intros t j Ht Hin [_ Hncomp].
    apply Hncomp.
    rewrite completed_iff_service_ge_cost.
    destruct llf_example_service_at_3 as [Hsvc0 [Hsvc1 Hsvc2]].
    destruct Hin as [Hj | [Hj | [Hj | []]]]; subst j.
    - rewrite <- Hsvc0.
      simpl.
      pose proof (service_job_monotone 2 llf_example_sched 0 3 t Ht) as Hmon.
      lia.
    - rewrite <- Hsvc1.
      simpl.
      pose proof (service_job_monotone 2 llf_example_sched 1 3 t Ht) as Hmon.
      lia.
    - rewrite <- Hsvc2.
      simpl.
      pose proof (service_job_monotone 2 llf_example_sched 2 3 t Ht) as Hmon.
      lia.
  Qed.

  Lemma llf_example_rel :
    scheduler_rel (global_llf_scheduler llf_example_candidates)
      llf_example_jobs 2 llf_example_sched.
  Proof.
    unfold global_llf_scheduler, top_m_algorithm_schedule.
    intros t c.
    destruct t as [|[|[|t']]].
    - destruct c as [|[|c']].
      + vm_compute. reflexivity.
      + vm_compute. reflexivity.
      + reflexivity.
    - destruct c as [|[|c']].
      + vm_compute. reflexivity.
      + vm_compute. reflexivity.
      + reflexivity.
    - destruct c as [|[|c']].
      + vm_compute. reflexivity.
      + vm_compute. reflexivity.
      + reflexivity.
    - destruct c as [|[|c']]; simpl.
      + change
          (None =
           nth_error
             (choose_top_m_by_metric 2
                (global_llf_metric_of_jobs llf_example_jobs 2 llf_example_sched (S (S (S t'))))
                llf_example_jobs 2 llf_example_sched (S (S (S t'))) [0; 1; 2]) 0).
        simpl.
        rewrite (choose_min_metric_none_if_no_eligible
                   (global_llf_metric_of_jobs llf_example_jobs 2 llf_example_sched (S (S (S t'))))
                   llf_example_jobs 2 llf_example_sched (S (S (S t'))) [0; 1; 2]).
        reflexivity.
        intros j Hin.
        eapply llf_example_not_eligible_after_3; eauto.
        lia.
      + change
          (None =
           nth_error
             (choose_top_m_by_metric 2
                (global_llf_metric_of_jobs llf_example_jobs 2 llf_example_sched (S (S (S t'))))
                llf_example_jobs 2 llf_example_sched (S (S (S t'))) [0; 1; 2]) 1).
        simpl.
        rewrite (choose_min_metric_none_if_no_eligible
                   (global_llf_metric_of_jobs llf_example_jobs 2 llf_example_sched (S (S (S t'))))
                   llf_example_jobs 2 llf_example_sched (S (S (S t'))) [0; 1; 2]).
        reflexivity.
        intros j Hin.
        eapply llf_example_not_eligible_after_3; eauto.
        lia.
      + reflexivity.
  Qed.

  Example global_llf_cpu0_has_le_laxity_than_excluded_job_example :
    (laxity llf_example_jobs 2 llf_example_sched 0%nat 1%nat <=
     laxity llf_example_jobs 2 llf_example_sched 2%nat 1%nat)%Z.
  Proof.
    eapply (global_llf_not_running_admissible_job_implies_running_job_has_le_laxity
              all_cpus_admissible llf_example_J llf_example_candidates
              llf_example_jobs 2 llf_example_sched 1%nat 2%nat 0%nat 0%nat).
    - exact (candidate_source_spec_to_admissible
               all_cpus_admissible llf_example_J llf_example_candidates
               llf_example_candidates_spec).
    - exact llf_example_rel.
    - unfold llf_example_J. lia.
    - apply admissible_somewhere_of_all_cpus_admissible.
      + lia.
      + unfold eligible, released, completed, llf_example_jobs, llf_job2.
        simpl.
        lia.
    - intros [cpu [Hlt Hrun]].
      destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate.
    - lia.
    - reflexivity.
  Qed.

  Example global_llf_cpu1_has_le_laxity_than_excluded_job_example :
    (laxity llf_example_jobs 2 llf_example_sched 1%nat 1%nat <=
     laxity llf_example_jobs 2 llf_example_sched 2%nat 1%nat)%Z.
  Proof.
    eapply (global_llf_not_running_admissible_job_implies_running_job_has_le_laxity
              all_cpus_admissible llf_example_J llf_example_candidates
              llf_example_jobs 2 llf_example_sched 1%nat 2%nat 1%nat 1%nat).
    - exact (candidate_source_spec_to_admissible
               all_cpus_admissible llf_example_J llf_example_candidates
               llf_example_candidates_spec).
    - exact llf_example_rel.
    - unfold llf_example_J. lia.
    - apply admissible_somewhere_of_all_cpus_admissible.
      + lia.
      + unfold eligible, released, completed, llf_example_jobs, llf_job2.
        simpl.
        lia.
    - intros [cpu [Hlt Hrun]].
      destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate.
    - lia.
    - reflexivity.
  Qed.

  Example global_llf_running_jobs_have_le_laxity_than_excluded_job_example :
    forall c, c < 2 ->
      exists j_run,
        llf_example_sched 1 c = Some j_run /\
        (laxity llf_example_jobs 2 llf_example_sched j_run 1%nat <=
         laxity llf_example_jobs 2 llf_example_sched 2%nat 1%nat)%Z.
  Proof.
    intros c Hc.
    eapply (global_llf_not_running_admissible_job_implies_running_jobs_have_le_laxity
              all_cpus_admissible llf_example_J llf_example_candidates
              llf_example_jobs 2 llf_example_sched 1%nat 2%nat).
    - exact (candidate_source_spec_to_admissible
               all_cpus_admissible llf_example_J llf_example_candidates
               llf_example_candidates_spec).
    - exact llf_example_rel.
    - unfold llf_example_J. lia.
    - apply admissible_somewhere_of_all_cpus_admissible.
      + lia.
      + unfold eligible, released, completed, llf_example_jobs, llf_job2.
        simpl.
        lia.
    - intros [cpu [Hlt Hrun]].
      destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate.
    - exact Hc.
  Qed.

  Example global_llf_excluded_eligible_job_implies_machine_full_example :
    forall c, c < 2 -> cpu_busy llf_example_sched 1 c.
  Proof.
    intros c Hc.
    exact
      (global_llf_not_running_eligible_job_implies_all_cpus_busy
         llf_example_J llf_example_candidates
         llf_example_jobs 2 llf_example_sched 1%nat 2%nat
         llf_example_candidates_spec
         llf_example_rel
         ltac:(lia)
         ltac:(unfold llf_example_J; lia)
         ltac:(unfold eligible, released, completed, llf_example_jobs, llf_job2; simpl; lia)
         ltac:(intros [cpu [Hlt Hrun]];
               destruct cpu as [|[|cpu']]; simpl in Hrun; discriminate)
         c Hc).
  Qed.

End GlobalLLFExamples.
