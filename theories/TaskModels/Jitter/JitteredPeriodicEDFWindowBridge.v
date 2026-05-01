From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
Import ListNotations.

Record jittered_periodic_edf_busy_prefix_no_carry_in_bridge
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (sched : Schedule)
    (j : JobId) : Prop := {
  jittered_periodic_edf_busy_prefix_no_carry_in_only :
    forall t1 t2,
      busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
      t1 <= job_release (jobs j) ->
      forall t j_run,
        job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
        sched t 0 = Some j_run ->
        jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
          t1 (job_abs_deadline (jobs j)) j_run ->
        job_release (jobs j) <= job_release (jobs j_run)
}.

Lemma NoDup_map_filter :
  forall A B (f : A -> B) (p : A -> bool) l,
    NoDup (map f l) ->
    NoDup (map f (filter p l)).
Proof.
  intros A B f p l Hnd.
  induction l as [|x l IH]; simpl in *.
  - constructor.
  - inversion Hnd as [|fx fl Hnotin Htail]; subst fx fl.
    destruct (p x) eqn:Hp; simpl.
    + constructor.
      * intro Hin.
        apply Hnotin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Hy Hin]].
        apply in_map_iff.
        exists y. split; [exact Hy|].
        apply filter_In in Hin.
        exact (proj1 Hin).
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.

Lemma edf_scheduler_nonidle_if_jittered_periodic_job_eligible :
  forall T tasks offset jitter jobs H enumJ sched t,
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    (exists j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j /\
      eligible jobs 1 sched j t) ->
    exists j', sched t 0 = Some j'.
Proof.
  intros T tasks offset jitter jobs H enumJ sched t
         HenumJ_complete HenumJ_sound Hsched [j [Hjobset Helig]].
  eapply single_cpu_algorithm_some_if_subset_eligible.
  - apply enum_candidates_spec.
    + exact HenumJ_complete.
    + exact HenumJ_sound.
  - exact Hsched.
  - exists j. split; assumption.
Qed.

Lemma edf_scheduled_job_in_jittered_periodic_jobset :
  forall T tasks offset jitter jobs H enumJ sched t j,
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    sched t 0 = Some j ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j.
Proof.
  intros T tasks offset jitter jobs H enumJ sched t j HenumJ_sound Hsched Hrun.
  pose proof (single_cpu_algorithm_eq_cpu0 edf_generic_spec (enum_candidates_of enumJ)
                jobs sched t Hsched) as Heq.
  apply HenumJ_sound.
  eapply choose_edf_in_candidates.
  rewrite Hrun in Heq.
  symmetry.
  exact Heq.
Qed.

Lemma edf_scheduled_job_deadline_le_eligible_jittered_periodic_job :
  forall T tasks offset jitter jobs H enumJ sched t j_run j_ref,
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    t < H ->
    sched t 0 = Some j_run ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j_ref ->
    eligible jobs 1 sched j_ref t ->
    job_abs_deadline (jobs j_run) <= job_abs_deadline (jobs j_ref).
Proof.
  intros T tasks offset jitter jobs H enumJ sched t j_run j_ref
         HenumJ_complete HenumJ_sound Hsched Ht Hrun Hjref Helig.
  pose proof
    (respects_edf_policy_at_with_implies_respects_edf_priority_at_on
       (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
       (enum_candidates_of enumJ)
       (enum_candidates_spec
          (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
          enumJ HenumJ_complete HenumJ_sound)
       jobs sched t) as Hprio0.
  assert (Hprio :
    respects_edf_priority_at_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      jobs sched t).
  {
    eapply Hprio0.
    eapply single_cpu_algorithm_schedule_respects_algorithm_spec_at_with.
    - exact choose_edf_refines_edf_policy.
    - exact Hsched.
  }
  pose proof (edf_scheduled_job_in_jittered_periodic_jobset
                T tasks offset jitter jobs H enumJ sched t j_run
                HenumJ_sound Hsched Hrun) as Hjrun.
  destruct (Nat.le_gt_cases (job_abs_deadline (jobs j_run))
                            (job_abs_deadline (jobs j_ref))) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    eapply Hprio.
    + exact Hjrun.
    + exact Hjref.
    + exact Hrun.
    + exact Helig.
    + exact Hgt.
Qed.

Lemma edf_busy_window_scheduled_jittered_periodic_job_release_ge_start :
  forall T tasks offset jitter jobs H enumJ sched t1 t2 t j,
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    sched t 0 = Some j ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    job_release (jobs j) >= t1.
Proof.
  intros T tasks offset jitter jobs H enumJ sched t1 t2 t j
         Hnonblocked HenumJ_complete HenumJ_sound Hsched Hbusy Ht1t Htt2 Hrun Hj.
  destruct (le_gt_dec t1 (job_release (jobs j))) as [Hge | Hlt].
  - exact Hge.
  - exfalso.
    pose proof (single_cpu_algorithm_valid edf_generic_spec (enum_candidates_of enumJ)
                  jobs sched Hsched) as Hvalid.
    assert (Hnotcomp_t : ~ completed jobs 1 sched j t).
    { eapply valid_no_run_after_completion; eauto. }
    destruct t1 as [|t1'].
    + lia.
    + assert (Hrel_pred : job_release (jobs j) <= t1') by lia.
      assert (Hnotcomp_pred : ~ completed jobs 1 sched j t1').
      { intro Hcomp.
        assert (Hcomp_t : completed jobs 1 sched j t).
        { apply (completed_monotone jobs 1 sched j t1' t); lia || exact Hcomp. }
        apply Hnotcomp_t.
        exact Hcomp_t.
      }
      assert (Hnblocked_pred : ~ blocked jobs j t1').
      { apply (Hnonblocked j t1' Hj). }
      assert (Helig_pred : eligible jobs 1 sched j t1').
      { repeat split; try exact Hrel_pred; try exact Hnotcomp_pred; exact Hnblocked_pred. }
      destruct (edf_scheduler_nonidle_if_jittered_periodic_job_eligible
                  T tasks offset jitter jobs H enumJ sched t1'
                  HenumJ_complete HenumJ_sound Hsched
                  (ex_intro _ j (conj Hj Helig_pred))) as [j' Hrun_pred].
      pose proof (busy_prefix_candidate_left_boundary sched (S t1') t2 Hbusy) as Hleft.
      destruct Hleft as [Hzero | Hidle].
      * discriminate.
      * apply Hidle.
        exists j'. exact Hrun_pred.
Qed.

Lemma edf_busy_window_scheduled_jittered_job_relevant_before_missed_deadline :
  forall T tasks offset jitter jobs H enumJ enumT sched t1 t2 t j_run j_miss,
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    t < H ->
    job_release (jobs j_miss) <= t ->
    t < job_abs_deadline (jobs j_miss) ->
    sched t 0 = Some j_run ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    jittered_periodic_jobset_deadline_between
      T tasks offset jitter jobs t1 (job_abs_deadline (jobs j_miss)) j_run /\
    In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jitter jobs H enumJ enumT sched t1 t2 t j_run j_miss
         Hnonblocked HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Ht1t Htt2 HtH Hrel_miss_t Hbefore_miss Hrun Hjmiss Hmiss.
  pose proof (edf_scheduled_job_in_jittered_periodic_jobset
                T tasks offset jitter jobs H enumJ sched t j_run
                HenumJ_sound Hsched Hrun) as Hjrun.
  pose proof (edf_busy_window_scheduled_jittered_periodic_job_release_ge_start
                T tasks offset jitter jobs H enumJ sched t1 t2 t j_run
                Hnonblocked HenumJ_complete HenumJ_sound Hsched Hbusy Ht1t Htt2 Hrun Hjrun)
    as Hrel_ge.
  pose proof (edf_scheduled_job_deadline_le_eligible_jittered_periodic_job
                T tasks offset jitter jobs H enumJ sched t j_run j_miss
                HenumJ_complete HenumJ_sound Hsched HtH Hrun Hjmiss) as Hdl_le.
  assert (Helig_miss : eligible jobs 1 sched j_miss t).
  {
    apply missed_deadline_job_eligible_before_deadline.
    - exact Hmiss.
    - exact Hrel_miss_t.
    - exact Hbefore_miss.
    - apply (Hnonblocked j_miss t Hjmiss).
  }
  specialize (Hdl_le Helig_miss).
  split.
  - split.
    + exact (jittered_periodic_jobset_upto_implies_task_in_scope
               T tasks offset jitter jobs H j_run Hjrun).
    + split.
      * exact (jittered_periodic_jobset_upto_implies_generated
                 T tasks offset jitter jobs H j_run Hjrun).
      * split; assumption.
  - apply HenumT_complete.
    exact (jittered_periodic_jobset_upto_implies_task_in_scope
             T tasks offset jitter jobs H j_run Hjrun).
Qed.

Lemma edf_busy_window_runs_relevant_jittered_job_before_missed_deadline :
  forall T tasks offset jitter jobs H enumJ enumT sched t1 t2 t j_miss,
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    t < H ->
    job_release (jobs j_miss) <= t ->
    t < job_abs_deadline (jobs j_miss) ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    exists j_run,
      sched t 0 = Some j_run /\
      jittered_periodic_jobset_deadline_between
        T tasks offset jitter jobs t1 (job_abs_deadline (jobs j_miss)) j_run /\
      In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jitter jobs H enumJ enumT sched t1 t2 t j_miss
         Hnonblocked HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Ht1t Htt2 HtH Hrel_miss_t Hbefore_miss Hjmiss Hmiss.
  destruct (edf_scheduler_nonidle_if_jittered_periodic_job_eligible
              T tasks offset jitter jobs H enumJ sched t
              HenumJ_complete HenumJ_sound Hsched) as [j_run Hrun].
  - exists j_miss.
    split.
    + exact Hjmiss.
    + apply missed_deadline_job_eligible_before_deadline; try assumption.
      apply (Hnonblocked j_miss t Hjmiss).
  - exists j_run.
    split.
    + exact Hrun.
    + eapply edf_busy_window_scheduled_jittered_job_relevant_before_missed_deadline; eauto.
Qed.

Lemma jittered_codec_window_relevant_job_in_filtered_list :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H)
         t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    jittered_periodic_jobset_deadline_between T tasks offset jitter jobs t1 t2 j ->
    job_release (jobs j) < H ->
    In j
      (filter (periodic_window_job_filter jobs t1 t2)
              (enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec)).
Proof.
  intros T tasks offset jitter jobs H enumT codec t1 t2 j Hwf HenumT Hwin Hrel_lt.
  apply filter_In.
  split.
  - eapply enum_jittered_periodic_jobs_upto_complete; eauto.
    + split.
      * exact (jittered_periodic_jobset_deadline_between_implies_task_in_scope
                 T tasks offset jitter jobs t1 t2 j Hwin).
      * split.
        -- exact (jittered_periodic_jobset_deadline_between_implies_generated
                    T tasks offset jitter jobs t1 t2 j Hwin).
        -- exact Hrel_lt.
  - apply periodic_window_job_filter_spec.
    split.
    + exact (jittered_periodic_jobset_deadline_between_implies_release_ge
               T tasks offset jitter jobs t1 t2 j Hwin).
    + exact (jittered_periodic_jobset_deadline_between_implies_deadline_le
               T tasks offset jitter jobs t1 t2 j Hwin).
Qed.

Lemma edf_missed_jittered_job_implies_relevant_prefix_overload_if_no_carry_in :
  forall T tasks offset jitter jobs H enumJ enumT
         (codec : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H)
         sched t1 t2 j_miss,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    t1 <= job_release (jobs j_miss) ->
    job_abs_deadline (jobs j_miss) <= t2 ->
    job_abs_deadline (jobs j_miss) <= H ->
    (forall t j_run,
      job_release (jobs j_miss) <= t < job_abs_deadline (jobs j_miss) ->
      sched t 0 = Some j_run ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
        t1 (job_abs_deadline (jobs j_miss)) j_run ->
      job_release (jobs j_miss) <= job_release (jobs j_run)) ->
    exists l,
      NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) /\
      (forall x, In x l ->
         jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
           (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) x /\
         In (job_task (jobs x)) enumT) /\
      cpu_service_between sched
        (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) <
      total_job_cost jobs l.
Proof.
  intros T tasks offset jitter jobs H enumJ enumT codec sched t1 t2 j_miss
         Hwf Hnonblocked HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Hjmiss Hmiss Ht1rel Hdl_le_t2 Hdl_le_H Hcarry_free.
  pose proof (single_cpu_algorithm_valid edf_generic_spec (enum_candidates_of enumJ)
                jobs sched Hsched) as Hvalid.
  set (a := job_release (jobs j_miss)).
  set (b := job_abs_deadline (jobs j_miss)).
  set (l := filter (periodic_window_job_filter jobs a b)
                   (enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec)).
  exists l.
  assert (Hnd_pairs :
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l)).
  { subst l.
    unfold enum_jittered_periodic_jobs_upto.
    eapply NoDup_map_filter.
    eapply NoDup_map_filter.
    eapply enum_jittered_periodic_jobs_upto_unfiltered_task_index_nodup; eauto. }
  assert (Hnd_l : NoDup l).
  { subst l.
    apply NoDup_filter.
    apply enum_jittered_periodic_jobs_upto_nodup; assumption. }
  assert (Hlprop :
    forall x, In x l ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
        (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) x /\
      In (job_task (jobs x)) enumT).
  { subst l a b.
    intros x Hinx.
    apply filter_In in Hinx.
    destruct Hinx as [HinEnum Hfilt].
    pose proof (enum_jittered_periodic_jobs_upto_sound
                  T tasks offset jitter jobs H enumT codec HenumT_sound x HinEnum)
      as Hjobset.
    apply periodic_window_job_filter_spec in Hfilt.
    destruct Hjobset as [HT [Hgen _]].
    destruct Hfilt as [Hrel Hdl].
    split.
    - split.
      + exact HT.
      + split.
        * exact Hgen.
        * split; assumption.
    - apply HenumT_complete.
      exact HT.
  }
  split; [exact Hnd_pairs|].
  split; [exact Hlprop|].
  assert (Hcover :
    forall t, a <= t < b ->
      exists j_run, sched t 0 = Some j_run /\ In j_run l).
  { intros t Hrange.
    subst a b.
    destruct (edf_busy_window_runs_relevant_jittered_job_before_missed_deadline
                T tasks offset jitter jobs H enumJ enumT sched t1 t2 t j_miss
                Hnonblocked HenumJ_complete HenumJ_sound HenumT_complete
                Hsched Hbusy
                (ltac:(lia)) (ltac:(lia)) (ltac:(lia))
                (proj1 Hrange) (proj2 Hrange) Hjmiss Hmiss)
      as [j_run [Hrun [Hrel_run Htask_run]]].
    exists j_run. split; [exact Hrun|].
    assert (Hrel_lt_H : job_release (jobs j_run) < H).
    { pose proof (valid_no_run_before_release jobs 1 sched j_run t 0 Hvalid) as Hrel_le.
      specialize (Hrel_le (Nat.lt_succ_diag_r 0) Hrun).
      lia. }
    eapply jittered_codec_window_relevant_job_in_filtered_list.
    - exact Hwf.
    - exact HenumT_complete.
    - destruct Hrel_run as [HT_run [Hgen_run [Hrel_run_t1 Hdl_run]]].
      split; [exact HT_run|].
      split; [exact Hgen_run|].
      split.
      + exact (Hcarry_free t j_run Hrange Hrun
                 (conj HT_run (conj Hgen_run (conj Hrel_run_t1 Hdl_run)))).
      + exact Hdl_run.
    - exact Hrel_lt_H.
  }
  assert (Hcpu_eq :
    cpu_service_between sched a b =
    total_service_between_list sched l a b).
  { apply total_service_between_list_covers_cpu_supply.
    - exact Hnd_l.
    - subst a b.
      pose proof (jittered_periodic_jobset_upto_implies_generated
                    T tasks offset jitter jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_by_jittered_periodic_deadline_eq
                    tasks offset jitter jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
    - exact Hcover.
  }
  assert (Hin_miss : In j_miss l).
  { subst l a b.
    eapply jittered_codec_window_relevant_job_in_filtered_list.
    - exact Hwf.
    - exact HenumT_complete.
    - split.
      + exact (jittered_periodic_jobset_upto_implies_task_in_scope
                 T tasks offset jitter jobs H j_miss Hjmiss).
      + split.
        * exact (jittered_periodic_jobset_upto_implies_generated
                   T tasks offset jitter jobs H j_miss Hjmiss).
        * split; lia.
    - exact (jittered_periodic_jobset_upto_implies_release_lt
               T tasks offset jitter jobs H j_miss Hjmiss).
  }
  apply in_split in Hin_miss.
  destruct Hin_miss as [l1 [l2 Hl_split]].
  subst l.
  rewrite Hcpu_eq.
  rewrite Hl_split.
  eapply (total_service_between_list_lt_total_job_cost_if_one_job_misses
            jobs sched l1 l2 j_miss
            (job_release (jobs j_miss))
            (job_abs_deadline (jobs j_miss))).
  - exact Hvalid.
  - subst a b.
    pose proof (jittered_periodic_jobset_upto_implies_generated
                  T tasks offset jitter jobs H j_miss Hjmiss) as Hgen_miss.
    pose proof (generated_by_jittered_periodic_deadline_eq
                  tasks offset jitter jobs j_miss Hgen_miss) as Hdl_eq.
    lia.
  - unfold service_between.
    rewrite (service_before_release_zero jobs 1 sched j_miss
               (job_release (jobs j_miss))).
    + rewrite Nat.sub_0_r.
      apply (proj1 (missed_deadline_iff_service_lt_cost_at_deadline jobs 1 sched j_miss)).
      exact Hmiss.
    + exact Hvalid.
    + lia.
  - apply total_service_between_list_le_total_job_cost.
    + exact Hvalid.
    + subst a b.
      pose proof (jittered_periodic_jobset_upto_implies_generated
                    T tasks offset jitter jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_by_jittered_periodic_deadline_eq
                    tasks offset jitter jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
  - apply total_service_between_list_le_total_job_cost.
    + exact Hvalid.
    + subst a b.
      pose proof (jittered_periodic_jobset_upto_implies_generated
                    T tasks offset jitter jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_by_jittered_periodic_deadline_eq
                    tasks offset jitter jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
Qed.

Lemma jittered_window_dbf_implies_no_deadline_miss_under_edf_if_no_carry_in :
  forall T tasks offset jitter H enumT enumJ jobs
         (codec : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    job_abs_deadline (jobs j) <= H ->
    (forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)) ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1' t2' <=
      t2' - t1') ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros T tasks offset jitter H enumT enumJ jobs codec sched j t1 t2
         Hwf Hnonblocked HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hj Hbusy Ht1 Hj_t2 Hj_H Hcarry_free Hdbf Hmiss.
  destruct (edf_missed_jittered_job_implies_relevant_prefix_overload_if_no_carry_in
              T tasks offset jitter jobs H enumJ enumT codec sched t1 t2 j
              Hwf Hnonblocked HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
              Hsched Hbusy Hj Hmiss Ht1 Hj_t2 Hj_H Hcarry_free)
    as [l [Hnd_l [Hlprop Hover]]].
  pose proof (jittered_periodic_total_window_demand_le_taskset_dbf_window
                T tasks offset jitter jobs
                (job_release (jobs j)) (job_abs_deadline (jobs j))
                enumT l Hwf HnodupT Hnd_l Hlprop) as Hdemand.
  pose proof (Hdbf (job_release (jobs j)) (job_abs_deadline (jobs j))) as Hdbf_j.
  assert (Hdbf_j' :
    taskset_jittered_periodic_dbf_window tasks offset jitter enumT
      (job_release (jobs j)) (job_abs_deadline (jobs j)) <=
    job_abs_deadline (jobs j) - job_release (jobs j)).
  {
    apply Hdbf_j.
    - pose proof (jittered_periodic_jobset_upto_implies_generated
                    T tasks offset jitter jobs H j Hj) as Hgen.
      pose proof (generated_by_jittered_periodic_deadline_eq
                    tasks offset jitter jobs j Hgen) as Hdl_eq.
      lia.
    - exact Hj_H.
  }
  destruct (Nat.lt_ge_cases (job_release (jobs j)) (job_abs_deadline (jobs j)))
    as [Hspan | Hnspan].
  - rewrite (busy_window_subinterval_cpu_supply_eq_length
               sched t1 t2 (job_release (jobs j)) (job_abs_deadline (jobs j)))
      in Hover by (try exact Hbusy; lia).
    lia.
  - assert (Heq :
        job_release (jobs j) = job_abs_deadline (jobs j)) by lia.
    rewrite Heq in Hover.
    rewrite cpu_service_between_refl in Hover.
    rewrite Heq in Hdbf_j'.
    simpl in Hdbf_j'.
    lia.
Qed.

Lemma edf_busy_prefix_start_before_release_if_jittered_missed :
  forall T tasks offset jitter jobs H enumJ sched j t1 t2,
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    (forall x, jittered_periodic_jobset_upto T tasks offset jitter jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> jittered_periodic_jobset_upto T tasks offset jitter jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    missed_deadline jobs 1 sched j ->
    t1 <= job_release (jobs j).
Proof.
  intros T tasks offset jitter jobs H enumJ sched j t1 t2
         Hnonblocked HenumJ_complete HenumJ_sound Hsched Hj Hwit Hmiss.
  destruct Hwit as [Hbusy [Ht1dl _]].
  destruct (Nat.le_gt_cases t1 (job_release (jobs j))) as [Hle | Hgt].
  - exact Hle.
  - destruct t1 as [|t1'].
    + lia.
    + pose proof (busy_prefix_candidate_left_boundary sched (S t1') t2 Hbusy) as Hleft.
      assert (Hrel_pred : job_release (jobs j) <= t1') by lia.
      assert (Hbefore_pred : t1' < job_abs_deadline (jobs j)) by lia.
      assert (Helig_pred : eligible jobs 1 sched j t1').
      { apply missed_deadline_job_eligible_before_deadline.
        - exact Hmiss.
        - exact Hrel_pred.
        - exact Hbefore_pred.
        - apply (Hnonblocked j t1' Hj). }
      destruct (edf_scheduler_nonidle_if_jittered_periodic_job_eligible
                  T tasks offset jitter jobs H enumJ sched t1'
                  HenumJ_complete HenumJ_sound Hsched
                  (ex_intro _ j (conj Hj Helig_pred))) as [j_run Hrun].
      destruct Hleft as [Hzero | Hidle].
      * discriminate.
      * exfalso.
        apply Hidle.
        exists j_run.
        exact Hrun.
Qed.

Theorem jittered_window_dbf_implies_no_deadline_miss_under_generated_edf_with_no_carry_in_bridge :
  forall T tasks offset jitter H enumT jobs
         (codec : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H)
         j,
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
    job_abs_deadline (jobs j) <= H ->
    jittered_periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jitter jobs H
      (generated_schedule
         edf_generic_spec
         (enum_candidates_of
            (enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec))
         jobs)
      j ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1' t2' <=
      t2' - t1') ->
    ~ missed_deadline jobs 1
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec))
           jobs)
        j.
Proof.
  intros T tasks offset jitter H enumT jobs codec j
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hj Hj_H Hbridge Hdbf.
  set (enumJ := enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec).
  set (sched :=
    generated_schedule edf_generic_spec (enum_candidates_of enumJ) jobs).
  assert (Hcand_spec :
    CandidateSourceSpec (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (enum_candidates_of enumJ)).
  { apply enum_candidates_spec.
    - exact (enum_jittered_periodic_jobs_upto_complete
               T tasks offset jitter jobs H enumT codec Hwf HenumT_complete).
    - exact (enum_jittered_periodic_jobs_upto_sound
               T tasks offset jitter jobs H enumT codec HenumT_sound).
  }
  assert (Hsched :
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched).
  {
    unfold sched.
    eapply
      (generated_schedule_scheduler_rel
         edf_generic_spec
         (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
         (enum_candidates_of enumJ)
         Hcand_spec
         jobs).
    intros s1 s2 t Hagree.
    eapply edf_choose_agrees_before; eauto.
  }
  intro Hmiss.
  assert (Helig :
    eligible jobs 1 sched j (job_abs_deadline (jobs j))).
  {
    repeat split.
    - pose proof (jittered_periodic_jobset_upto_implies_generated
                    T tasks offset jitter jobs H j Hj) as Hgen.
      pose proof (generated_by_jittered_periodic_deadline_eq
                    tasks offset jitter jobs j Hgen) as Hdl_eq.
      unfold released.
      lia.
    - exact Hmiss.
    - apply (Hnonblocked j (job_abs_deadline (jobs j)) Hj).
  }
  assert (Hbusy_at_deadline :
    cpu_busy_at sched (job_abs_deadline (jobs j))).
  {
    destruct (edf_scheduler_nonidle_if_jittered_periodic_job_eligible
                T tasks offset jitter jobs H enumJ sched
                (job_abs_deadline (jobs j))
                (enum_jittered_periodic_jobs_upto_complete
                   T tasks offset jitter jobs H enumT codec Hwf HenumT_complete)
                (enum_jittered_periodic_jobs_upto_sound
                   T tasks offset jitter jobs H enumT codec HenumT_sound)
                Hsched) as [j_run Hrun].
    - exists j. split; assumption.
    - exists j_run. exact Hrun.
  }
  destruct (busy_prefix_witness_exists_from_busy_time
              sched (job_abs_deadline (jobs j)) Hbusy_at_deadline)
    as [t1 [t2 Hwit]].
  assert (Ht1rel : t1 <= job_release (jobs j)).
  { eapply edf_busy_prefix_start_before_release_if_jittered_missed; eauto using
      enum_jittered_periodic_jobs_upto_complete, enum_jittered_periodic_jobs_upto_sound. }
  assert (Hcarry_free :
    forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      jittered_periodic_jobset_deadline_between T tasks offset jitter jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)).
  {
    intros t j_run Hbetween Hrun Hdeadline_between.
    eapply jittered_periodic_edf_busy_prefix_no_carry_in_only; eauto.
  }
  pose proof
    (jittered_window_dbf_implies_no_deadline_miss_under_edf_if_no_carry_in
       T tasks offset jitter H enumT enumJ jobs codec sched j t1 t2
       Hwf Hnonblocked HnodupT HenumT_sound
       (enum_jittered_periodic_jobs_upto_complete T tasks offset jitter jobs H enumT codec
          Hwf HenumT_complete)
       (enum_jittered_periodic_jobs_upto_sound T tasks offset jitter jobs H enumT codec
          HenumT_sound)
       HenumT_complete
       Hsched Hj (proj1 Hwit) Ht1rel (proj2 (proj2 Hwit)) Hj_H Hcarry_free Hdbf) as Hnmiss.
  exact (Hnmiss Hmiss).
Qed.

Theorem jittered_window_dbf_implies_edf_feasible_on_finite_horizon_with_no_carry_in_bridge :
  forall T tasks offset jitter H enumT jobs
         (codec : JitteredPeriodicFiniteHorizonCodec T tasks offset jitter jobs H),
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec))
           jobs)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1.
Proof.
  intros T tasks offset jitter H enumT jobs codec
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hjob_bridge Hdbf.
  set (enumJ := enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec).
  set (sched := generated_schedule edf_generic_spec (enum_candidates_of enumJ) jobs).
  assert (Hcand_spec :
    CandidateSourceSpec (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (enum_candidates_of enumJ)).
  { apply enum_candidates_spec.
    - exact (enum_jittered_periodic_jobs_upto_complete
               T tasks offset jitter jobs H enumT codec Hwf HenumT_complete).
    - exact (enum_jittered_periodic_jobs_upto_sound
               T tasks offset jitter jobs H enumT codec HenumT_sound).
  }
  assert (Hsched :
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched).
  {
    unfold sched.
    eapply
      (generated_schedule_scheduler_rel
         edf_generic_spec
         (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
         (enum_candidates_of enumJ)
         Hcand_spec
         jobs).
    intros s1 s2 t Hagree.
    eapply edf_choose_agrees_before; eauto.
  }
  exists sched.
  split.
  - eapply single_cpu_algorithm_valid.
    exact Hsched.
  - unfold feasible_schedule_on.
    intros j Hj.
    destruct (Hjob_bridge j Hj) as [Hj_H Hbridge].
    unfold sched, enumJ in *.
    eapply jittered_window_dbf_implies_no_deadline_miss_under_generated_edf_with_no_carry_in_bridge; eauto.
Qed.

Theorem jittered_periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_no_carry_in_bridge :
  forall T T_bool tasks offset jitter H enumT jobs
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    (forall τ, T_bool τ = true <-> T τ) ->
    well_formed_periodic_tasks_on T tasks ->
    jittered_periodic_jobset_nonblocking T tasks offset jitter jobs H ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_jittered_periodic_jobs_upto
                 T tasks offset jitter jobs H enumT codec))
           jobs)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_jittered_periodic_jobs_upto
               T tasks offset jitter jobs H enumT codec)))
      jobs 1.
Proof.
  intros T T_bool tasks offset jitter H enumT jobs codec
         HTbool Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hjob_bridge Hdbf.
  set (enumJ := enum_jittered_periodic_jobs_upto T tasks offset jitter jobs H enumT codec).
  set (sched := generated_schedule edf_generic_spec (enum_candidates_of enumJ) jobs).
  assert (Hcand_spec :
    CandidateSourceSpec (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
      (enum_candidates_of enumJ)).
  { apply enum_candidates_spec.
    - exact (enum_jittered_periodic_jobs_upto_complete
               T tasks offset jitter jobs H enumT codec Hwf HenumT_complete).
    - exact (enum_jittered_periodic_jobs_upto_sound
               T tasks offset jitter jobs H enumT codec HenumT_sound).
  }
  assert (Hsched :
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched).
  {
    unfold sched.
    eapply
      (generated_schedule_scheduler_rel
         edf_generic_spec
         (jittered_periodic_jobset_upto T tasks offset jitter jobs H)
         (enum_candidates_of enumJ)
         Hcand_spec
         jobs).
    intros s1 s2 t Hagree.
    eapply edf_choose_agrees_before; eauto.
  }
  assert (Hfeas :
    feasible_on (jittered_periodic_jobset_upto T tasks offset jitter jobs H) jobs 1).
  {
    unfold enumJ, sched.
    eapply jittered_window_dbf_implies_edf_feasible_on_finite_horizon_with_no_carry_in_bridge;
      eauto.
  }
  eapply jittered_periodic_finite_optimality_lift.
  - intros J J_bool enumJ' cands cand_spec jobs' Hb Hnb Hc Hs Hf.
    exact
      (edf_optimality_on_finite_jobs
         J J_bool enumJ' cands cand_spec jobs' Hb Hnb Hc Hs Hf).
  - exact HTbool.
  - exact Hnonblocked.
  - eapply enum_jittered_periodic_jobs_upto_complete; eauto.
  - eapply enum_jittered_periodic_jobs_upto_sound; eauto.
  - exact Hfeas.
Qed.
