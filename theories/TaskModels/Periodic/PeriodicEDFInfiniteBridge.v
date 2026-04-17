From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFNoCarryInSupply.

Definition generated_periodic_edf_schedule
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs) : Schedule :=
  generated_schedule
    edf_generic_spec
    (periodic_candidates_before T tasks offset jobs enumT codec)
    jobs.

Definition generated_periodic_edf_schedule_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs) : Schedule :=
  generated_schedule
    edf_generic_spec
    (enum_candidates_of
       (enum_periodic_jobs_upto
          T tasks offset jobs H enumT
          (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
    jobs.

Lemma generated_periodic_edf_schedule_scheduler_rel :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    scheduler_rel
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset jobs enumT codec.
  unfold generated_periodic_edf_schedule.
  exact
    (infinite_generated_edf_scheduler_rel
       T tasks offset jobs enumT codec).
Qed.

Lemma generated_periodic_edf_schedule_valid :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    valid_schedule
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset jobs enumT codec.
  eapply single_cpu_algorithm_valid.
    exact
      (generated_periodic_edf_schedule_scheduler_rel
         T tasks offset jobs enumT codec).
Qed.

Lemma generated_periodic_edf_schedule_upto_scheduler_rel :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto
               T tasks offset jobs H enumT
               (periodic_finite_horizon_codec_of T tasks offset jobs H codec))))
      jobs 1
      (generated_periodic_edf_schedule_upto T tasks offset jobs H enumT codec).
Proof.
  intros T tasks offset jobs H enumT codec
         Hwf HenumT_complete HenumT_sound.
  set (enumJ :=
         enum_periodic_jobs_upto
           T tasks offset jobs H enumT
           (periodic_finite_horizon_codec_of T tasks offset jobs H codec)).
  assert (Hcand_spec :
    CandidateSourceSpec (periodic_jobset_upto T tasks offset jobs H)
      (enum_candidates_of enumJ)).
  {
    apply enum_candidates_spec.
    - exact
        (enum_periodic_jobs_upto_complete
           T tasks offset jobs H enumT
           (periodic_finite_horizon_codec_of T tasks offset jobs H codec)
           Hwf HenumT_complete).
    - exact
        (enum_periodic_jobs_upto_sound
           T tasks offset jobs H enumT
           (periodic_finite_horizon_codec_of T tasks offset jobs H codec)
           HenumT_sound).
  }
  unfold generated_periodic_edf_schedule_upto.
  eapply generated_schedule_scheduler_rel with
    (J := periodic_jobset_upto T tasks offset jobs H)
    (cand_spec := Hcand_spec).
  intros s1 s2 t Hagree.
  eapply edf_choose_agrees_before; eauto.
Qed.

Lemma generated_periodic_edf_schedule_upto_valid :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    valid_schedule jobs 1
    (generated_periodic_edf_schedule_upto T tasks offset jobs H enumT codec).
Proof.
  intros T tasks offset jobs H enumT codec
         Hwf HenumT_complete HenumT_sound.
  eapply single_cpu_algorithm_valid.
  exact
    (generated_periodic_edf_schedule_upto_scheduler_rel
       T tasks offset jobs H enumT codec
       Hwf HenumT_complete HenumT_sound).
Qed.

Lemma periodic_edf_prefix_cpu0_eq_choose_top :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs) t,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    generated_periodic_edf_schedule_upto
      T tasks offset jobs H enumT codec t 0 =
    choose_edf jobs 1
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs H enumT codec)
      t
      (enum_periodic_jobs_upto
         T tasks offset jobs H enumT
         (periodic_finite_horizon_codec_of T tasks offset jobs H codec)).
Proof.
  intros T tasks offset jobs H enumT codec t
         Hwf HenumT_complete HenumT_sound.
  set (enumJ :=
         enum_periodic_jobs_upto
           T tasks offset jobs H enumT
           (periodic_finite_horizon_codec_of T tasks offset jobs H codec)).
  exact
    (single_cpu_algorithm_eq_cpu0
       edf_generic_spec
       (enum_candidates_of enumJ)
       jobs
       (generated_periodic_edf_schedule_upto
          T tasks offset jobs H enumT codec)
       t
       (generated_periodic_edf_schedule_upto_scheduler_rel
          T tasks offset jobs H enumT codec
          Hwf HenumT_complete HenumT_sound)).
Qed.

Lemma periodic_job_eligible_at_release_generic :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs) τ k,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    T τ ->
    expected_release tasks offset τ k < H ->
    0 < job_cost (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) ->
    eligible jobs 1
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs H enumT codec)
      (global_periodic_job_id_of T tasks offset jobs codec τ k)
      (expected_release tasks offset τ k).
Proof.
  intros T tasks offset jobs H enumT codec τ k
         Hwf HenumT_complete HenumT_sound Hτ Hrel Hcost_pos.
  split.
  - unfold released.
    pose proof
      (global_periodic_job_id_of_sound T tasks offset jobs codec τ k Hτ)
      as [Htask [Hidx Hgen]].
    rewrite (generated_job_release tasks offset jobs _ Hgen).
    rewrite Htask, Hidx.
    reflexivity.
  - apply not_completed_iff_service_lt_cost.
    pose proof
      (global_periodic_job_id_of_sound T tasks offset jobs codec τ k Hτ)
      as [Htask [Hidx Hgen]].
    assert (Hrelease :
      job_release (jobs (global_periodic_job_id_of T tasks offset jobs codec τ k)) =
      expected_release tasks offset τ k).
    {
      rewrite (generated_job_release tasks offset jobs _ Hgen).
      rewrite Htask, Hidx.
      reflexivity.
    }
    rewrite <- Hrelease.
    rewrite (service_at_release_zero
               jobs 1
               (generated_periodic_edf_schedule_upto
                  T tasks offset jobs H enumT codec)
               (global_periodic_job_id_of T tasks offset jobs codec τ k)).
    + exact Hcost_pos.
    + apply generated_periodic_edf_schedule_upto_valid; assumption.
Qed.

Lemma generated_periodic_edf_schedule_upto_agrees_before_generated :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         H,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    agrees_before
      (generated_periodic_edf_schedule_upto T tasks offset jobs H enumT codec)
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
      H.
Proof.
  intros T tasks offset jobs enumT codec H
         Hwf HenumT_complete HenumT_sound.
  exact
    (infinite_generated_edf_prefix_coherence
       T tasks offset jobs enumT codec
       Hwf HenumT_complete HenumT_sound H).
Qed.

Lemma generated_periodic_edf_schedule_upto_completed_iff_generated_before :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs)
         H j t,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    t < H ->
    completed
      jobs 1
      (generated_periodic_edf_schedule_upto T tasks offset jobs H enumT codec)
      j t <->
    completed
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
      j t.
Proof.
  intros T tasks offset jobs enumT codec H j t
         Hwf HenumT_complete HenumT_sound Ht.
  apply agrees_before_completed.
  apply
    (agrees_before_weaken
       (generated_periodic_edf_schedule_upto T tasks offset jobs H enumT codec)
       (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
       t H).
  - lia.
  - exact
      (generated_periodic_edf_schedule_upto_agrees_before_generated
         T tasks offset jobs enumT codec H
         Hwf HenumT_complete HenumT_sound).
Qed.

Lemma periodic_jobset_implies_upto_deadline_succ :
  forall T tasks offset jobs j,
    periodic_jobset T tasks offset jobs j ->
    periodic_jobset_upto
      T tasks offset jobs (S (job_abs_deadline (jobs j))) j.
Proof.
  intros T tasks offset jobs j [HT Hgen].
  split.
  - exact HT.
  - split.
    + exact Hgen.
    + pose proof (generated_job_deadline tasks offset jobs j Hgen) as Hdl.
      lia.
Qed.

Theorem periodic_edf_no_deadline_miss_from_window_dbf :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_bridge
      T tasks offset jobs (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
      j ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    ~ missed_deadline jobs 1
        (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
        j.
Proof.
  intros T tasks offset enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound
         Hj Hbridge Hdbf.
  set (HH := S (job_abs_deadline (jobs j))).
  set (sched_fin :=
    generated_periodic_edf_schedule_upto T tasks offset jobs HH enumT codec).
  set (sched_inf :=
    generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  assert (Hjob_upto :
    periodic_jobset_upto T tasks offset jobs HH j).
  { unfold HH. exact (periodic_jobset_implies_upto_deadline_succ T tasks offset jobs j Hj). }
  assert (Hfin_no_miss :
    ~ missed_deadline jobs 1 sched_fin j).
  {
    unfold sched_fin, generated_periodic_edf_schedule_upto, HH.
    eapply periodic_window_dbf_implies_no_deadline_miss_under_generated_edf_with_busy_prefix_bridge.
    - exact Hwf.
    - exact HnodupT.
    - exact HenumT_complete.
    - exact HenumT_sound.
    - exact Hjob_upto.
    - lia.
    - exact Hbridge.
    - intros t1 t2 Hle1 Hle2.
      exact (Hdbf t1 t2 Hle1).
  }
  unfold missed_deadline in *.
  intro Hmiss_inf.
  assert (Hagree_deadline :
    agrees_before sched_fin sched_inf (job_abs_deadline (jobs j))).
  {
    apply (agrees_before_weaken sched_fin sched_inf
             (job_abs_deadline (jobs j)) HH).
    - unfold HH. lia.
    - exact (infinite_generated_edf_prefix_coherence
               T tasks offset jobs enumT codec
               Hwf HenumT_complete HenumT_sound HH).
  }
  destruct (agrees_before_completed
              jobs 1
              sched_fin
              sched_inf
              j
              (job_abs_deadline (jobs j))
              Hagree_deadline) as [Hcomp_fin _].
  apply Hfin_no_miss.
  intro Hcomp_fin'.
  apply Hmiss_inf.
  apply Hcomp_fin.
  exact Hcomp_fin'.
Qed.

(* Canonical infinite generated-EDF entry point: only the schedule-local
   no-carry-in bridge remains as a user obligation. The release-boundary
   fact for the contradiction witness is derived internally from a deadline
   miss. *)
Theorem periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
      j ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    ~ missed_deadline jobs 1
        (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
        j.
Proof.
  intros T tasks offset enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound
         Hj Hbridge Hdbf.
  set (HH := S (job_abs_deadline (jobs j))).
  set (sched_fin :=
    generated_periodic_edf_schedule_upto T tasks offset jobs HH enumT codec).
  set (sched_inf :=
    generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  assert (Hjob_upto :
    periodic_jobset_upto T tasks offset jobs HH j).
  { unfold HH. exact (periodic_jobset_implies_upto_deadline_succ T tasks offset jobs j Hj). }
  assert (Hfin_no_miss :
    ~ missed_deadline jobs 1 sched_fin j).
  {
    unfold sched_fin, generated_periodic_edf_schedule_upto, HH.
    eapply periodic_window_dbf_implies_no_deadline_miss_under_generated_edf_with_no_carry_in_bridge.
    - exact Hwf.
    - exact HnodupT.
    - exact HenumT_complete.
    - exact HenumT_sound.
    - exact Hjob_upto.
    - lia.
    - exact Hbridge.
    - intros t1 t2 Hle1 Hle2.
      exact (Hdbf t1 t2 Hle1).
  }
  unfold missed_deadline in *.
  intro Hmiss_inf.
  assert (Hagree_deadline :
    agrees_before sched_fin sched_inf (job_abs_deadline (jobs j))).
  {
    apply (agrees_before_weaken sched_fin sched_inf
             (job_abs_deadline (jobs j)) HH).
    - unfold HH. lia.
    - exact (infinite_generated_edf_prefix_coherence
               T tasks offset jobs enumT codec
               Hwf HenumT_complete HenumT_sound HH).
  }
  destruct (agrees_before_completed
              jobs 1
              sched_fin
              sched_inf
              j
              (job_abs_deadline (jobs j))
              Hagree_deadline) as [Hcomp_fin _].
  apply Hfin_no_miss.
  intro Hcomp_fin'.
  apply Hmiss_inf.
  apply Hcomp_fin.
  exact Hcomp_fin'.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_schedule_on
      (periodic_jobset T tasks offset jobs)
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  eapply periodic_edf_no_deadline_miss_from_window_dbf; eauto.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    feasible_schedule_on
      (periodic_jobset T tasks offset jobs)
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge; eauto.
Qed.

Theorem periodic_edf_no_deadline_miss_from_classical_dbf :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_bridge
      T tasks offset jobs (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
      j ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    ~ missed_deadline jobs 1
        (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
        j.
Proof.
  intros T tasks offset enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hj Hbridge Hdbf.
  eapply periodic_edf_no_deadline_miss_from_window_dbf; eauto.
  intros t1 t2 Hle.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + exact Hoff.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf.
Qed.

Theorem periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs)
         j,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    periodic_jobset T tasks offset jobs j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T tasks offset jobs (S (job_abs_deadline (jobs j)))
      (generated_periodic_edf_schedule_upto
         T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
      j ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    ~ missed_deadline jobs 1
        (generated_periodic_edf_schedule T tasks offset jobs enumT codec)
        j.
Proof.
  intros T tasks offset enumT jobs codec j
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hj Hbridge Hdbf.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge; eauto.
  intros t1 t2 Hle.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + exact Hoff.
    + intros τ Hin. apply Hwf. apply HenumT_sound. exact Hin.
  - apply Hdbf.
Qed.

Theorem periodic_edf_feasible_schedule_from_classical_dbf :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    feasible_schedule_on
      (periodic_jobset T tasks offset jobs)
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hbridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  eapply periodic_edf_no_deadline_miss_from_classical_dbf; eauto.
Qed.

Theorem periodic_edf_feasible_schedule_from_classical_dbf_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    feasible_schedule_on
      (periodic_jobset T tasks offset jobs)
      jobs 1
      (generated_periodic_edf_schedule T tasks offset jobs enumT codec).
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hbridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  eapply periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge; eauto.
Qed.

Theorem periodic_edf_schedulable_by_on :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  - apply infinite_generated_edf_scheduler_rel.
  - eapply single_cpu_algorithm_valid.
    apply infinite_generated_edf_scheduler_rel.
  - eapply periodic_edf_feasible_schedule_from_window_dbf; eauto.
Qed.

Theorem periodic_edf_schedulable_by_on_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  - apply infinite_generated_edf_scheduler_rel.
  - eapply single_cpu_algorithm_valid.
    apply infinite_generated_edf_scheduler_rel.
  - eapply periodic_edf_feasible_schedule_from_window_dbf_with_no_carry_in_bridge; eauto.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hbridge Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  - apply infinite_generated_edf_scheduler_rel.
  - eapply single_cpu_algorithm_valid.
    apply infinite_generated_edf_scheduler_rel.
  - eapply periodic_edf_feasible_schedule_from_classical_dbf_with_no_carry_in_bridge; eauto.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  exact periodic_edf_schedulable_by_on.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_on :
  forall T tasks offset enumT jobs
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_busy_prefix_bridge
        T tasks offset jobs (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall t, taskset_periodic_dbf tasks enumT t <= t) ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound Hoff
         Hbridge Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_periodic_edf_schedule T tasks offset jobs enumT codec).
  - apply infinite_generated_edf_scheduler_rel.
  - eapply single_cpu_algorithm_valid.
    apply infinite_generated_edf_scheduler_rel.
  - eapply periodic_edf_feasible_schedule_from_classical_dbf; eauto.
Qed.
