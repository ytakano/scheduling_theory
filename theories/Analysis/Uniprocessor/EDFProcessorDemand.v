From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleTransform.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.

Import ListNotations.

Lemma edf_deadline_miss_implies_busy_window_covering_deadline :
  forall (jobs : JobId -> Job) sched j t1 t2,
    missed_deadline jobs 1 sched j ->
    busy_window_candidate sched t1 t2 ->
    t1 <= job_abs_deadline (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j t1 t2 Hmiss Hbusy Hleft Hright.
  exact (deadline_miss_inside_busy_window_candidate jobs sched j t1 t2
           Hmiss Hbusy Hleft Hright).
Qed.

Lemma periodic_window_overload_contradiction :
  forall T tasks offset jobs enumT sched t1 t2 l,
    well_formed_periodic_tasks_on T tasks ->
    busy_window_candidate sched t1 t2 ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall x, In x l ->
       periodic_jobset_deadline_between T tasks offset jobs t1 t2 x /\
       In (job_task (jobs x)) enumT) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1 ->
    cpu_service_between sched t1 t2 < total_job_cost jobs l ->
    False.
Proof.
  intros T tasks offset jobs enumT sched t1 t2 l
         Hwf Hbusy HnodupT HnodupL Hl Hdbf Hover.
  pose proof (periodic_total_window_demand_le_taskset_dbf_window
                T tasks offset jobs t1 t2 enumT l
                Hwf HnodupT HnodupL Hl) as Hdemand.
  rewrite busy_window_candidate_cpu_supply_eq_length in Hover by exact Hbusy.
  lia.
Qed.

Lemma window_dbf_bound_implies_no_window_overload :
  forall T tasks offset jobs enumT sched t1 t2 l,
    well_formed_periodic_tasks_on T tasks ->
    busy_window_candidate sched t1 t2 ->
    NoDup enumT ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    (forall x, In x l ->
       periodic_jobset_deadline_between T tasks offset jobs t1 t2 x /\
       In (job_task (jobs x)) enumT) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1 ->
    total_job_cost jobs l <= cpu_service_between sched t1 t2.
Proof.
  intros T tasks offset jobs enumT sched t1 t2 l
         Hwf Hbusy HnodupT HnodupL Hl Hdbf.
  destruct (le_gt_dec (total_job_cost jobs l) (cpu_service_between sched t1 t2))
    as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    eapply periodic_window_overload_contradiction; eauto.
Qed.

Definition periodic_window_job_filter
    (jobs : JobId -> Job) (t1 t2 : Time) (j : JobId) : bool :=
  Nat.leb t1 (job_release (jobs j))
  && Nat.leb (job_abs_deadline (jobs j)) t2.

Lemma periodic_window_job_filter_spec :
  forall jobs t1 t2 j,
    periodic_window_job_filter jobs t1 t2 j = true <->
    t1 <= job_release (jobs j) /\ job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs t1 t2 j.
  unfold periodic_window_job_filter.
  rewrite andb_true_iff.
  rewrite !Nat.leb_le.
  tauto.
Qed.

Lemma codec_window_relevant_jobs_exist :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         t1 t2,
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup
      (map (fun j => (job_task (jobs j), job_index (jobs j)))
           (filter (periodic_window_job_filter jobs t1 t2)
                   (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))) /\
    (forall x, In x (filter (periodic_window_job_filter jobs t1 t2)
                            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)) ->
       periodic_jobset_deadline_between T tasks offset jobs t1 t2 x /\
       In (job_task (jobs x)) enumT).
Proof.
  intros T tasks offset jobs H enumT codec t1 t2 HnodupT HenumT.
  split.
  - eapply periodic_filtered_pairs_nodup_window.
    eapply enum_periodic_jobs_upto_task_index_nodup; eauto.
  - intros x Hinx.
    apply filter_In in Hinx.
    destruct Hinx as [HinEnum Hwin].
    pose proof (enum_periodic_jobs_upto_sound T tasks offset jobs H enumT codec HenumT x HinEnum)
      as Hjobset.
    unfold enum_periodic_jobs_upto in HinEnum.
    apply in_flat_map in HinEnum.
    destruct HinEnum as [τ [Hτin Hjmap]].
    apply in_map_iff in Hjmap.
    destruct Hjmap as [k [Hx Hkin]].
    apply periodic_window_job_filter_spec in Hwin.
    destruct Hjobset as [HT [Hgen _]].
    destruct Hwin as [Hrel Hdl].
    split.
    + split.
      * exact HT.
      * split.
        -- exact Hgen.
        -- split.
           ++ exact Hrel.
           ++ exact Hdl.
    + subst x.
      pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ k
                    (HenumT τ Hτin)
                    (proj2 (proj1 (in_enum_periodic_indices_upto_iff tasks offset τ H k) Hkin)))
        as [Htask [_ _]].
      rewrite Htask.
      exact Hτin.
Qed.

Lemma edf_scheduler_periodic_respects_priority_at :
  forall T tasks offset jobs H enumJ sched t,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    t < H ->
    respects_edf_priority_at_on (periodic_jobset_upto T tasks offset jobs H) jobs sched t.
Proof.
  intros T tasks offset jobs H enumJ sched t HenumJ_complete HenumJ_sound Hsched Ht.
  eapply respects_edf_policy_at_with_implies_respects_edf_priority_at_on.
  - apply enum_candidates_spec.
    + exact HenumJ_complete.
    + exact HenumJ_sound.
  - eapply single_cpu_algorithm_schedule_respects_algorithm_spec_at_with.
    + exact choose_edf_refines_edf_policy.
    + exact Hsched.
Qed.

Lemma edf_scheduler_nonidle_if_periodic_job_eligible :
  forall T tasks offset jobs H enumJ sched t,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    (exists j, periodic_jobset_upto T tasks offset jobs H j /\ eligible jobs 1 sched j t) ->
    exists j', sched t 0 = Some j'.
Proof.
  intros T tasks offset jobs H enumJ sched t HenumJ_complete HenumJ_sound Hsched
         [j [Hjobset Helig]].
  eapply single_cpu_algorithm_some_if_subset_eligible.
  - apply enum_candidates_spec.
    + exact HenumJ_complete.
    + exact HenumJ_sound.
  - exact Hsched.
  - exists j. split; assumption.
Qed.

Lemma edf_scheduled_job_in_periodic_jobset :
  forall T tasks offset jobs H enumJ sched t j,
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    sched t 0 = Some j ->
    periodic_jobset_upto T tasks offset jobs H j.
Proof.
  intros T tasks offset jobs H enumJ sched t j HenumJ_sound Hsched Hrun.
  pose proof (single_cpu_algorithm_eq_cpu0 edf_generic_spec (enum_candidates_of enumJ)
                jobs sched t Hsched) as Heq.
  apply HenumJ_sound.
  eapply choose_edf_in_candidates.
  rewrite Hrun in Heq.
  symmetry.
  exact Heq.
Qed.

Lemma edf_scheduled_job_deadline_le_eligible_periodic_job :
  forall T tasks offset jobs H enumJ sched t j_run j_ref,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    t < H ->
    sched t 0 = Some j_run ->
    periodic_jobset_upto T tasks offset jobs H j_ref ->
    eligible jobs 1 sched j_ref t ->
    job_abs_deadline (jobs j_run) <= job_abs_deadline (jobs j_ref).
Proof.
  intros T tasks offset jobs H enumJ sched t j_run j_ref
         HenumJ_complete HenumJ_sound Hsched Ht Hrun Hjref Helig.
  pose proof (edf_scheduler_periodic_respects_priority_at
                T tasks offset jobs H enumJ sched t
                HenumJ_complete HenumJ_sound Hsched Ht)
    as Hprio.
  pose proof (edf_scheduled_job_in_periodic_jobset
                T tasks offset jobs H enumJ sched t j_run
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

Lemma edf_busy_window_scheduled_periodic_job_release_ge_start :
  forall T tasks offset jobs H enumJ sched t1 t2 t j,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    sched t 0 = Some j ->
    periodic_jobset_upto T tasks offset jobs H j ->
    job_release (jobs j) >= t1.
Proof.
  intros T tasks offset jobs H enumJ sched t1 t2 t j
         HenumJ_complete HenumJ_sound Hsched Hbusy Ht1t Htt2 Hrun Hj.
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
        { apply (completed_monotone jobs 1 sched j t1' t).
          - lia.
          - exact Hcomp.
        }
        apply Hnotcomp_t.
        exact Hcomp_t.
      }
      assert (Helig_pred : eligible jobs 1 sched j t1').
      { split; [exact Hrel_pred | exact Hnotcomp_pred]. }
      destruct (edf_scheduler_nonidle_if_periodic_job_eligible
                  T tasks offset jobs H enumJ sched t1'
                  HenumJ_complete HenumJ_sound Hsched
                  (ex_intro _ j (conj Hj Helig_pred))) as [j' Hrun_pred].
      pose proof (busy_prefix_candidate_left_boundary sched (S t1') t2 Hbusy) as Hleft.
      destruct Hleft as [Hzero | Hidle].
      * discriminate.
      * apply Hidle.
        exists j'. exact Hrun_pred.
Qed.

Lemma edf_busy_window_scheduled_job_relevant_before_reference_deadline :
  forall T tasks offset jobs H enumJ enumT sched t1 t2 t j_run j_ref,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    t < H ->
    sched t 0 = Some j_run ->
    periodic_jobset_upto T tasks offset jobs H j_ref ->
    eligible jobs 1 sched j_ref t ->
    periodic_jobset_deadline_between T tasks offset jobs t1 (job_abs_deadline (jobs j_ref)) j_run /\
    In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jobs H enumJ enumT sched t1 t2 t j_run j_ref
         HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Ht1t Htt2 HtH Hrun Hjref Helig_ref.
  pose proof (edf_scheduled_job_in_periodic_jobset
                T tasks offset jobs H enumJ sched t j_run
                HenumJ_sound Hsched Hrun) as Hjrun.
  pose proof (edf_busy_window_scheduled_periodic_job_release_ge_start
                T tasks offset jobs H enumJ sched t1 t2 t j_run
                HenumJ_complete HenumJ_sound Hsched Hbusy Ht1t Htt2 Hrun Hjrun)
    as Hrel_ge.
  pose proof (edf_scheduled_job_deadline_le_eligible_periodic_job
                T tasks offset jobs H enumJ sched t j_run j_ref
                HenumJ_complete HenumJ_sound Hsched)
    as Hdl_le.
  specialize (Hdl_le HtH Hrun Hjref Helig_ref).
  split.
  - destruct Hjrun as [HT [Hgen _]].
    split.
    + exact HT.
    + split.
      * exact Hgen.
      * split.
        -- exact Hrel_ge.
        -- exact Hdl_le.
  - apply HenumT_complete.
    exact (periodic_jobset_upto_implies_task_in_scope T tasks offset jobs H j_run Hjrun).
Qed.

Lemma missed_deadline_job_eligible_before_deadline :
  forall jobs sched j t,
    missed_deadline jobs 1 sched j ->
    job_release (jobs j) <= t ->
    t < job_abs_deadline (jobs j) ->
    eligible jobs 1 sched j t.
Proof.
  intros jobs sched j t Hmiss Hrel Hbefore.
  split.
  - exact Hrel.
  - intro Hcomp_t.
    apply Hmiss.
    apply (completed_monotone jobs 1 sched j t (job_abs_deadline (jobs j))).
    + lia.
    + exact Hcomp_t.
Qed.

Lemma edf_busy_window_scheduled_job_relevant_before_missed_deadline :
  forall T tasks offset jobs H enumJ enumT sched t1 t2 t j_run j_miss,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    t < H ->
    job_release (jobs j_miss) <= t ->
    t < job_abs_deadline (jobs j_miss) ->
    sched t 0 = Some j_run ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    periodic_jobset_deadline_between T tasks offset jobs t1 (job_abs_deadline (jobs j_miss)) j_run /\
    In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jobs H enumJ enumT sched t1 t2 t j_run j_miss
         HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Ht1t Htt2 HtH Hrel_miss_t Hbefore_miss Hrun Hjmiss Hmiss.
  eapply edf_busy_window_scheduled_job_relevant_before_reference_deadline; eauto.
  apply missed_deadline_job_eligible_before_deadline.
  - exact Hmiss.
  - exact Hrel_miss_t.
  - exact Hbefore_miss.
Qed.

Lemma edf_busy_window_runs_relevant_job_before_missed_deadline :
  forall T tasks offset jobs H enumJ enumT sched t1 t2 t j_miss,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t < t2 ->
    t < H ->
    job_release (jobs j_miss) <= t ->
    t < job_abs_deadline (jobs j_miss) ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    exists j_run,
      sched t 0 = Some j_run /\
      periodic_jobset_deadline_between T tasks offset jobs t1 (job_abs_deadline (jobs j_miss)) j_run /\
      In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jobs H enumJ enumT sched t1 t2 t j_miss
         HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Ht1t Htt2 HtH Hrel_miss_t Hbefore_miss Hjmiss Hmiss.
  destruct (edf_scheduler_nonidle_if_periodic_job_eligible
              T tasks offset jobs H enumJ sched t
              HenumJ_complete HenumJ_sound Hsched) as [j_run Hrun].
  - exists j_miss.
    split.
    + exact Hjmiss.
    + apply missed_deadline_job_eligible_before_deadline; assumption.
  - exists j_run.
    split.
    + exact Hrun.
    + exact (edf_busy_window_scheduled_job_relevant_before_missed_deadline
               T tasks offset jobs H enumJ enumT sched t1 t2 t j_run j_miss
               HenumJ_complete HenumJ_sound HenumT_complete
               Hsched Hbusy Ht1t Htt2 HtH Hrel_miss_t Hbefore_miss Hrun Hjmiss Hmiss).
Qed.

Lemma edf_release_deadline_slots_are_relevant_if_no_carry_in :
  forall T tasks offset jobs H enumJ enumT sched t1 t2 j_miss,
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    t1 <= job_release (jobs j_miss) ->
    job_abs_deadline (jobs j_miss) <= t2 ->
    job_abs_deadline (jobs j_miss) <= H ->
    (forall t j_run,
      job_release (jobs j_miss) <= t < job_abs_deadline (jobs j_miss) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j_miss)) j_run ->
      job_release (jobs j_miss) <= job_release (jobs j_run)) ->
    forall t,
      job_release (jobs j_miss) <= t < job_abs_deadline (jobs j_miss) ->
      exists j_run,
        sched t 0 = Some j_run /\
        periodic_jobset_deadline_between T tasks offset jobs
          (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) j_run /\
        In (job_task (jobs j_run)) enumT.
Proof.
  intros T tasks offset jobs H enumJ enumT sched t1 t2 j_miss
         HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Hjmiss Hmiss Ht1rel Hdl_le_t2 Hdl_le_H Hcarry_free
         t Hrange.
  destruct (edf_busy_window_runs_relevant_job_before_missed_deadline
              T tasks offset jobs H enumJ enumT sched t1 t2 t j_miss
              HenumJ_complete HenumJ_sound HenumT_complete
              Hsched Hbusy) as [j_run [Hrun [Hrel_t1 Htask]]].
  - lia.
  - lia.
  - lia.
  - exact (proj1 Hrange).
  - exact (proj2 Hrange).
  - exact Hjmiss.
  - exact Hmiss.
  - exists j_run.
    split; [exact Hrun|].
    split.
    + destruct Hrel_t1 as [HT [Hgen [Hrel_t1' Hdl]]].
      split; [exact HT|].
      split; [exact Hgen|].
      split.
      * exact (Hcarry_free t j_run Hrange Hrun
                 (conj HT (conj Hgen (conj Hrel_t1' Hdl)))).
      * exact Hdl.
    + exact Htask.
Qed.

Lemma busy_window_subinterval_cpu_supply_eq_length :
  forall sched t1 t2 a b,
    busy_prefix_candidate sched t1 t2 ->
    t1 <= a ->
    a < b ->
    b <= t2 ->
    cpu_service_between sched a b = b - a.
Proof.
  intros sched t1 t2 a b Hbusy Ha Hab Hb.
  apply cpu_service_between_busy_interval_eq_length.
  apply busy_interval_suffix with (t1 := t1).
  - apply busy_interval_prefix with (t2 := t2).
    + exact (busy_prefix_candidate_busy_interval sched t1 t2 Hbusy).
    + lia.
    + exact Hb.
  - exact Ha.
  - lia.
Qed.

Lemma missed_deadline_busy_prefix_supply_eq_length :
  forall T tasks offset jobs H enumJ sched t1 t2 j_miss,
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    t1 <= job_release (jobs j_miss) ->
    job_abs_deadline (jobs j_miss) <= t2 ->
    job_release (jobs j_miss) < job_abs_deadline (jobs j_miss) ->
    cpu_service_between sched (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) =
    job_abs_deadline (jobs j_miss) - job_release (jobs j_miss).
Proof.
  intros T tasks offset jobs H enumJ sched t1 t2 j_miss
         _ Hsched Hbusy Hjmiss Hrel_ge Hdl_le Hspan.
  exact (busy_window_subinterval_cpu_supply_eq_length
           sched t1 t2 (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss))
           Hbusy Hrel_ge Hspan Hdl_le).
Qed.

Lemma missed_deadline_service_between_release_deadline_lt_cost :
  forall T tasks offset jobs H sched j_miss,
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    valid_schedule jobs 1 sched ->
    missed_deadline jobs 1 sched j_miss ->
    service_between 1 sched j_miss
      (job_release (jobs j_miss))
      (job_abs_deadline (jobs j_miss)) <
    job_cost (jobs j_miss).
Proof.
  intros T tasks offset jobs H sched j_miss Hjmiss Hvalid Hmiss.
  unfold service_between.
  rewrite (service_before_release_zero jobs 1 sched j_miss
             (job_release (jobs j_miss))).
  - rewrite Nat.sub_0_r.
    apply (proj1 (missed_deadline_iff_service_lt_cost_at_deadline jobs 1 sched j_miss)).
    exact Hmiss.
  - exact Hvalid.
  - lia.
Qed.

Lemma missed_deadline_service_between_window_start_deadline_lt_cost :
  forall T tasks offset jobs H sched t1 j_miss,
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    valid_schedule jobs 1 sched ->
    missed_deadline jobs 1 sched j_miss ->
    t1 <= job_release (jobs j_miss) ->
    service_between 1 sched j_miss t1 (job_abs_deadline (jobs j_miss)) <
    job_cost (jobs j_miss).
Proof.
  intros T tasks offset jobs H sched t1 j_miss Hjmiss Hvalid Hmiss Ht1rel.
  unfold service_between.
  rewrite (service_before_release_zero jobs 1 sched j_miss t1).
  - rewrite Nat.sub_0_r.
    apply (proj1 (missed_deadline_iff_service_lt_cost_at_deadline jobs 1 sched j_miss)).
    exact Hmiss.
  - exact Hvalid.
  - exact Ht1rel.
Qed.

Fixpoint total_service_between_list
    (sched : Schedule) (l : list JobId) (t1 t2 : Time) : nat :=
  match l with
  | [] => 0
  | j :: l' =>
      service_between 1 sched j t1 t2 +
      total_service_between_list sched l' t1 t2
  end.

Lemma total_service_between_list_refl :
  forall sched l t,
    total_service_between_list sched l t t = 0.
Proof.
  intros sched l t.
  induction l as [|j l IH]; simpl.
  - reflexivity.
  - rewrite service_between_refl, IH. lia.
Qed.

Lemma total_service_between_list_split :
  forall sched l t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    total_service_between_list sched l t1 t3 =
    total_service_between_list sched l t1 t2 +
    total_service_between_list sched l t2 t3.
Proof.
  intros sched l t1 t2 t3 H12 H23.
  induction l as [|j l IH]; simpl.
  - reflexivity.
  - rewrite (service_between_split 1 sched j t1 t2 t3) by lia.
    rewrite IH by lia.
    lia.
Qed.

Lemma total_service_between_list_app :
  forall sched l1 l2 t1 t2,
    total_service_between_list sched (l1 ++ l2) t1 t2 =
    total_service_between_list sched l1 t1 t2 +
    total_service_between_list sched l2 t1 t2.
Proof.
  intros sched l1 l2 t1 t2.
  induction l1 as [|j l1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma service_between_single_slot_running :
  forall sched j t,
    sched t 0 = Some j ->
    service_between 1 sched j t (S t) = 1.
Proof.
  intros sched j t Hrun.
  unfold service_between.
  rewrite service_job_step_uni.
  apply runs_on_true_iff in Hrun.
  rewrite Hrun.
  lia.
Qed.

Lemma service_between_single_slot_not_running :
  forall sched j t,
    sched t 0 <> Some j ->
    service_between 1 sched j t (S t) = 0.
Proof.
  intros sched j t Hnrun.
  unfold service_between.
  rewrite service_job_step_uni.
  apply runs_on_false_iff in Hnrun.
  rewrite Hnrun.
  lia.
Qed.

Lemma total_service_between_list_single_slot_none :
  forall sched l t,
    (forall j, In j l -> sched t 0 <> Some j) ->
    total_service_between_list sched l t (S t) = 0.
Proof.
  intros sched l t Hnone.
  induction l as [|j l IH]; simpl.
  - reflexivity.
  - rewrite service_between_single_slot_not_running.
    + rewrite IH by (intros j' Hin; apply Hnone; now right).
      lia.
    + apply Hnone. now left.
Qed.

Lemma total_service_between_list_single_slot :
  forall sched l t,
    NoDup l ->
    (exists j_run, sched t 0 = Some j_run /\ In j_run l) ->
    total_service_between_list sched l t (S t) = 1.
Proof.
  intros sched l t Hnodup [j_run [Hrun Hin]].
  induction l as [|j l IH]; simpl in *.
  - contradiction.
  - inversion Hnodup as [|j' l' Hnotin HnodupTail]; subst j' l'.
    destruct Hin as [Heq | HinTail].
    + subst j.
      rewrite service_between_single_slot_running by exact Hrun.
      rewrite total_service_between_list_single_slot_none.
      * lia.
      * intros j' Hin'.
        intro HeqRun.
        apply Hnotin.
        rewrite HeqRun in Hrun.
        injection Hrun as HeqJob.
        subst j'.
        exact Hin'.
    + rewrite service_between_single_slot_not_running.
      * assert (Htail :
          total_service_between_list sched l t (S t) = 1).
        { exact (IH HnodupTail HinTail). }
        rewrite Htail.
        lia.
      * intro HeqRun.
        apply Hnotin.
        rewrite HeqRun in Hrun.
        injection Hrun as HeqJob.
        subst j.
        exact HinTail.
Qed.

Lemma total_service_between_list_covers_cpu_supply :
  forall sched l t1 t2,
    NoDup l ->
    t1 <= t2 ->
    (forall t, t1 <= t < t2 -> exists j_run, sched t 0 = Some j_run /\ In j_run l) ->
    cpu_service_between sched t1 t2 =
    total_service_between_list sched l t1 t2.
Proof.
  intros sched l t1 t2 Hnodup Hle12 Hcover.
  remember (t2 - t1) as n eqn:Heqn.
  revert t1 t2 Hle12 Heqn Hcover.
  induction n as [|n IH]; intros t1 t2 Hle12 Heqn Hcover.
  - symmetry in Heqn.
    assert (t2 = t1) by lia.
    subst t2.
    rewrite cpu_service_between_refl.
    rewrite total_service_between_list_refl.
    reflexivity.
  - assert (Ht1t2 : t1 < t2) by lia.
    rewrite (cpu_service_between_split sched t1 (S t1) t2) by lia.
    rewrite (total_service_between_list_split sched l t1 (S t1) t2) by lia.
    assert (Hslot :
      cpu_service_between sched t1 (S t1) =
      total_service_between_list sched l t1 (S t1)).
    { specialize (Hcover t1).
      assert (Ht1range : t1 <= t1 < t2) by lia.
      destruct (Hcover Ht1range) as [j_run [Hrun Hin]].
      unfold cpu_service_between.
      rewrite cumulative_cpu_service_step.
      assert (Hcpu : cpu_service_at sched t1 = 1).
      { apply cpu_busy_at_cpu_service_one.
        exists j_run. exact Hrun. }
      rewrite Hcpu.
      rewrite (total_service_between_list_single_slot sched l t1 Hnodup).
      - lia.
      - eauto.
    }
    assert (Hrest :
      cpu_service_between sched (S t1) t2 =
      total_service_between_list sched l (S t1) t2).
    { apply IH.
      - lia.
      - lia.
      - intros t Hrange.
        apply Hcover. lia.
    }
    rewrite Hslot, Hrest.
    lia.
Qed.

Lemma total_service_between_list_le_total_job_cost :
  forall jobs sched l t1 t2,
    valid_schedule jobs 1 sched ->
    t1 <= t2 ->
    total_service_between_list sched l t1 t2 <= total_job_cost jobs l.
Proof.
  intros jobs sched l t1 t2 Hvalid Hle.
  induction l as [|j l IH]; simpl.
  - lia.
  - rewrite (service_between_eq 1 sched j t1 t2) by lia.
    pose proof (valid_schedule_1_service_le_cost jobs sched j t2 Hvalid) as Hcost.
    lia.
Qed.

Lemma codec_window_relevant_job_in_filtered_list :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         t1 t2 j,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    periodic_jobset_deadline_between T tasks offset jobs t1 t2 j ->
    job_release (jobs j) < H ->
    In j
      (filter (periodic_window_job_filter jobs t1 t2)
              (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)).
Proof.
  intros T tasks offset jobs H enumT codec t1 t2 j Hwf HenumT Hwin Hrel_lt.
  apply filter_In.
  split.
  - eapply enum_periodic_jobs_upto_complete; eauto.
    + split.
      * exact (periodic_jobset_deadline_between_implies_task_in_scope
                 T tasks offset jobs t1 t2 j Hwin).
      * split.
        -- exact (periodic_jobset_deadline_between_implies_generated
                    T tasks offset jobs t1 t2 j Hwin).
        -- exact Hrel_lt.
  - apply periodic_window_job_filter_spec.
    split.
    + exact (periodic_jobset_deadline_between_implies_release_ge
               T tasks offset jobs t1 t2 j Hwin).
    + exact (periodic_jobset_deadline_between_implies_deadline_le
               T tasks offset jobs t1 t2 j Hwin).
Qed.

Lemma total_service_between_list_lt_total_job_cost_if_one_job_misses :
  forall jobs sched l1 l2 j t1 t2,
    valid_schedule jobs 1 sched ->
    t1 <= t2 ->
    service_between 1 sched j t1 t2 < job_cost (jobs j) ->
    total_service_between_list sched l1 t1 t2 <= total_job_cost jobs l1 ->
    total_service_between_list sched l2 t1 t2 <= total_job_cost jobs l2 ->
    total_service_between_list sched (l1 ++ j :: l2) t1 t2 <
    total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros jobs sched l1 l2 j t1 t2 _ Hle Hmiss Hle1 Hle2.
  rewrite !total_service_between_list_app.
  simpl.
  rewrite !total_job_cost_app.
  simpl.
  lia.
Qed.

Lemma edf_missed_job_implies_relevant_prefix_overload :
  forall T tasks offset jobs H enumJ enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched t1 t2 j_miss,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    t1 <= job_release (jobs j_miss) ->
    job_abs_deadline (jobs j_miss) <= t2 ->
    job_abs_deadline (jobs j_miss) <= H ->
    (forall t,
      job_release (jobs j_miss) <= t < job_abs_deadline (jobs j_miss) ->
      exists j_run,
        sched t 0 = Some j_run /\
        periodic_jobset_deadline_between T tasks offset jobs
          (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) j_run /\
        In (job_task (jobs j_run)) enumT) ->
    exists l,
      NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) /\
      (forall x, In x l ->
         periodic_jobset_deadline_between T tasks offset jobs
           (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) x /\
         In (job_task (jobs x)) enumT) /\
      cpu_service_between sched
        (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) <
      total_job_cost jobs l.
Proof.
  intros T tasks offset jobs H enumJ enumT codec sched t1 t2 j_miss
         Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Hjmiss Hmiss Ht1rel Hdl_le_t2 Hdl_le_H Hrelevant_run.
  pose proof (single_cpu_algorithm_valid edf_generic_spec (enum_candidates_of enumJ)
                jobs sched Hsched) as Hvalid.
  set (a := job_release (jobs j_miss)).
  set (b := job_abs_deadline (jobs j_miss)).
  set (l := filter (periodic_window_job_filter jobs a b)
                   (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)).
  exists l.
  assert (Hnd_pairs :
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l)).
  { subst l a b.
    apply periodic_filtered_pairs_nodup_window.
    apply enum_periodic_jobs_upto_task_index_nodup.
    - exact HnodupT.
    - exact HenumT_sound.
  }
  assert (Hnd_l :
    NoDup l).
  { subst l a b.
    apply NoDup_filter.
    apply enum_periodic_jobs_upto_nodup.
    - exact HnodupT.
    - exact HenumT_sound.
  }
  assert (Hlprop :
    forall x, In x l ->
      periodic_jobset_deadline_between T tasks offset jobs
        (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) x /\
      In (job_task (jobs x)) enumT).
  { subst l a b.
    intros x Hinx.
    apply filter_In in Hinx.
    destruct Hinx as [HinEnum Hfilt].
    pose proof (enum_periodic_jobs_upto_sound T tasks offset jobs H enumT codec
                  HenumT_sound x HinEnum) as Hjobset.
    apply periodic_window_job_filter_spec in Hfilt.
    destruct Hjobset as [HT [Hgen _]].
    destruct Hfilt as [Hrel Hdl].
    split.
    - split; [exact HT|].
      split; [exact Hgen|].
      split; assumption.
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
    destruct (Hrelevant_run t Hrange) as [j_run [Hrun [Hrel_run Htask_run]]].
    - exists j_run. split; [exact Hrun|].
      assert (Hrel_lt_H : job_release (jobs j_run) < H).
      { pose proof (valid_no_run_before_release jobs 1 sched j_run t 0 Hvalid) as Hrel_le.
        specialize (Hrel_le (Nat.lt_succ_diag_r 0) Hrun).
        lia.
      }
      eapply codec_window_relevant_job_in_filtered_list.
      + exact Hwf.
      + exact HenumT_complete.
      + exact Hrel_run.
      + exact Hrel_lt_H.
  }
  assert (Hcpu_eq :
    cpu_service_between sched a b =
    total_service_between_list sched l a b).
  { apply total_service_between_list_covers_cpu_supply.
    - exact Hnd_l.
    - subst a b.
      pose proof (periodic_jobset_upto_implies_generated
                    T tasks offset jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_job_deadline tasks offset jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
    - exact Hcover.
  }
  assert (Hin_miss : In j_miss l).
  { subst l a b.
    eapply codec_window_relevant_job_in_filtered_list.
    - exact Hwf.
    - exact HenumT_complete.
    - split.
      * exact (periodic_jobset_upto_implies_task_in_scope T tasks offset jobs H j_miss Hjmiss).
      * split.
        -- exact (periodic_jobset_upto_implies_generated T tasks offset jobs H j_miss Hjmiss).
        -- split.
           ++ lia.
           ++ lia.
    - exact (periodic_jobset_upto_implies_release_lt T tasks offset jobs H j_miss Hjmiss).
  }
  apply in_split in Hin_miss.
  destruct Hin_miss as [l1 [l2 Hl_split]].
  subst l.
  rewrite Hcpu_eq.
  rewrite Hl_split.
  eapply total_service_between_list_lt_total_job_cost_if_one_job_misses.
  - exact Hvalid.
  - subst a b.
    pose proof (periodic_jobset_upto_implies_generated
                  T tasks offset jobs H j_miss Hjmiss) as Hgen_miss.
    pose proof (generated_job_deadline tasks offset jobs j_miss Hgen_miss) as Hdl_eq.
    lia.
  - exact (missed_deadline_service_between_release_deadline_lt_cost
             T tasks offset jobs H sched j_miss Hjmiss Hvalid Hmiss).
  - apply total_service_between_list_le_total_job_cost.
    + exact Hvalid.
    + subst a b.
      pose proof (periodic_jobset_upto_implies_generated
                    T tasks offset jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_job_deadline tasks offset jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
  - apply total_service_between_list_le_total_job_cost.
    + exact Hvalid.
    + subst a b.
      pose proof (periodic_jobset_upto_implies_generated
                    T tasks offset jobs H j_miss Hjmiss) as Hgen_miss.
      pose proof (generated_job_deadline tasks offset jobs j_miss Hgen_miss) as Hdl_eq.
      lia.
Qed.

Lemma edf_missed_job_implies_relevant_prefix_overload_if_no_carry_in :
  forall T tasks offset jobs H enumJ enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched t1 t2 j_miss,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    busy_prefix_candidate sched t1 t2 ->
    periodic_jobset_upto T tasks offset jobs H j_miss ->
    missed_deadline jobs 1 sched j_miss ->
    t1 <= job_release (jobs j_miss) ->
    job_abs_deadline (jobs j_miss) <= t2 ->
    job_abs_deadline (jobs j_miss) <= H ->
    (forall t j_run,
      job_release (jobs j_miss) <= t < job_abs_deadline (jobs j_miss) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j_miss)) j_run ->
      job_release (jobs j_miss) <= job_release (jobs j_run)) ->
    exists l,
      NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) /\
      (forall x, In x l ->
         periodic_jobset_deadline_between T tasks offset jobs
           (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) x /\
         In (job_task (jobs x)) enumT) /\
      cpu_service_between sched
        (job_release (jobs j_miss)) (job_abs_deadline (jobs j_miss)) <
      total_job_cost jobs l.
Proof.
  intros T tasks offset jobs H enumJ enumT codec sched t1 t2 j_miss
         Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hbusy Hjmiss Hmiss Ht1rel Hdl_le_t2 Hdl_le_H Hcarry_free.
  eapply edf_missed_job_implies_relevant_prefix_overload; eauto.
  eapply edf_release_deadline_slots_are_relevant_if_no_carry_in; eauto.
Qed.

Lemma periodic_window_dbf_implies_no_deadline_miss_under_edf_if_no_carry_in :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    job_abs_deadline (jobs j) <= H ->
    (forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)) ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1' t2' <= t2' - t1') ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros T tasks offset H enumT enumJ jobs codec sched j t1 t2
         Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hj Hbusy Ht1 Hj_t2 Hj_H Hcarry_free Hdbf Hmiss.
  destruct (edf_missed_job_implies_relevant_prefix_overload_if_no_carry_in
              T tasks offset jobs H enumJ enumT codec sched t1 t2 j
              Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
              Hsched Hbusy Hj Hmiss Ht1 Hj_t2 Hj_H Hcarry_free)
    as [l [Hnd_l [Hlprop Hover]]].
  pose proof (periodic_total_window_demand_le_taskset_dbf_window
                T tasks offset jobs
                (job_release (jobs j)) (job_abs_deadline (jobs j))
                enumT l Hwf HnodupT Hnd_l Hlprop) as Hdemand.
  pose proof (missed_deadline_busy_prefix_supply_eq_length
                T tasks offset jobs H enumJ sched t1 t2 j
                HenumJ_sound Hsched Hbusy Hj Ht1 Hj_t2) as Hsupply.
  pose proof (periodic_jobset_upto_implies_generated
                T tasks offset jobs H j Hj) as Hgen.
  pose proof (generated_job_deadline tasks offset jobs j Hgen) as Hdl_eq.
  pose proof (Hdbf (job_release (jobs j)) (job_abs_deadline (jobs j))) as Hdbf_j.
  assert (Hdbf_j' :
    taskset_periodic_dbf_window tasks offset enumT
      (job_release (jobs j)) (job_abs_deadline (jobs j)) <=
    job_abs_deadline (jobs j) - job_release (jobs j)).
  { apply Hdbf_j; lia. }
  destruct (Nat.lt_ge_cases (job_release (jobs j)) (job_abs_deadline (jobs j)))
    as [Hspan | Hnspan].
  - specialize (Hsupply Hspan).
    rewrite Hsupply in Hover.
    lia.
  - assert (Heq :
        job_release (jobs j) = job_abs_deadline (jobs j)) by lia.
    rewrite Heq in Hover.
    rewrite cpu_service_between_refl in Hover.
    rewrite Heq in Hdbf_j'.
    simpl in Hdbf_j'.
    lia.
Qed.

Lemma periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_prefix_and_no_carry_in :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= H ->
    (forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)) ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1' t2' <= t2' - t1') ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros T tasks offset H enumT enumJ jobs codec sched j t1 t2
         Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hj Hwit Ht1rel Hj_H Hcarry_free Hdbf.
  destruct Hwit as [Hbusy [Hdl_ge Hdl_le]].
  eapply periodic_window_dbf_implies_no_deadline_miss_under_edf_if_no_carry_in; eauto.
Qed.

Lemma periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_window_and_no_carry_in :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    (forall τ, T τ -> In τ enumT) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= H ->
    (forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)) ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1' t2' <= t2' - t1') ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros T tasks offset H enumT enumJ jobs codec sched j t1 t2
         Hwf HnodupT HenumT_sound HenumJ_complete HenumJ_sound HenumT_complete
         Hsched Hj Hwit Ht1rel Hj_H Hcarry_free Hdbf.
  eapply periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_prefix_and_no_carry_in;
    eauto using busy_window_witness_implies_busy_prefix_witness.
Qed.

(* ===== EDF feasibility from window-DBF ===== *)

(* The exported processor-demand theorem lives at the stronger interface that
   the existing proof pipeline can justify: an explicit busy-window witness and
   the schedule-local no-carry-in bridge are required. *)
Theorem periodic_window_dbf_implies_no_deadline_miss_under_edf :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1 sched ->
    periodic_jobset_upto T tasks offset jobs H j ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= H ->
    (forall t j_run,
      job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
      sched t 0 = Some j_run ->
      periodic_jobset_deadline_between T tasks offset jobs
        t1 (job_abs_deadline (jobs j)) j_run ->
      job_release (jobs j) <= job_release (jobs j_run)) ->
    (forall t1' t2',
      t1' <= t2' ->
      t2' <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1' t2' <= t2' - t1') ->
    ~ missed_deadline jobs 1 sched j.
Proof.
  intros T tasks offset H enumT jobs codec sched j t1 t2
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hj Hwit Ht1rel Hj_H Hcarry_free Hdbf.
  eapply
    periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_window_and_no_carry_in
    with (codec := codec)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec);
    eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.

(* The finite-horizon theorem packages the EDF witness schedule and the
   schedule-local no-miss property above. *)
Theorem periodic_window_dbf_implies_edf_feasible_on_finite_horizon :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1 sched ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      exists t1 t2,
        busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2 /\
        t1 <= job_release (jobs j) /\
        (forall t j_run,
          job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
          sched t 0 = Some j_run ->
          periodic_jobset_deadline_between T tasks offset jobs
            t1 (job_abs_deadline (jobs j)) j_run ->
          job_release (jobs j) <= job_release (jobs j_run))) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  exists sched.
  split.
  - eapply single_cpu_algorithm_valid.
    exact Hsched.
  - unfold feasible_schedule_on.
    intros j Hj.
    destruct (Hjob_bridge j Hj) as
        [Hj_H [t1 [t2 [Hwit [Ht1rel Hcarry_free]]]]].
    eapply periodic_window_dbf_implies_no_deadline_miss_under_edf
      with (codec := codec) (t1 := t1) (t2 := t2); eauto.
Qed.

Theorem periodic_window_dbf_implies_edf_feasible_on_finite_horizon_with_busy_prefix :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1 sched ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      exists t1 t2,
        busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 /\
        t1 <= job_release (jobs j) /\
        (forall t j_run,
          job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
          sched t 0 = Some j_run ->
          periodic_jobset_deadline_between T tasks offset jobs
            t1 (job_abs_deadline (jobs j)) j_run ->
          job_release (jobs j) <= job_release (jobs j_run))) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  exists sched.
  split.
  - eapply single_cpu_algorithm_valid.
    exact Hsched.
  - unfold feasible_schedule_on.
    intros j Hj.
    destruct (Hjob_bridge j Hj) as
        [Hj_H [t1 [t2 [Hwit [Ht1rel Hcarry_free]]]]].
    eapply periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_prefix_and_no_carry_in
      with (codec := codec)
           (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec)
           (t1 := t1) (t2 := t2); eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.
