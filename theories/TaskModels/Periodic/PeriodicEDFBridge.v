From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
Import ListNotations.

Theorem periodic_edf_optimality_on_finite_horizon :
  forall T T_bool tasks offset H enumJ jobs,
    (forall τ, T_bool τ = true <-> T τ) ->
    (forall j, periodic_jobset_upto T tasks offset jobs H j -> In j enumJ) ->
    (forall j, In j enumJ -> periodic_jobset_upto T tasks offset jobs H j) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas.
  exact (periodic_finite_optimality_lift edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T T_bool tasks offset H enumJ jobs HTbool Henum_complete Henum_sound Hfeas).
Qed.

(* Auto version: derive the job enumeration from a task list and a codec,
   eliminating the need to hand-write enumJ and its soundness/completeness proofs. *)
Theorem periodic_edf_optimality_on_finite_horizon_auto :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec Hwf HenumT_complete HenumT_sound Hfeas.
  exact (periodic_finite_optimality_lift_auto edf_scheduler
    (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
      edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
    T tasks offset H enumT jobs codec Hwf HenumT_complete HenumT_sound Hfeas).
Qed.

Theorem periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
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
         Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched Hj Hwit Ht1rel Hj_H
         Hcarry_free Hdbf.
  eapply
    periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_window_and_no_carry_in;
    eauto.
Qed.

Theorem periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_auto :
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
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon
    with (codec := codec)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec);
    eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.

Theorem periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_with_busy_prefix :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched j t1 t2,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
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
         Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched Hj Hwit Ht1rel Hj_H
         Hcarry_free Hdbf.
  eapply
    periodic_window_dbf_implies_no_deadline_miss_under_edf_if_covering_busy_prefix_and_no_carry_in;
    eauto.
Qed.

Theorem periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_auto_with_busy_prefix :
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
  intros T tasks offset H enumT jobs codec sched j t1 t2
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hj Hwit Ht1rel Hj_H Hcarry_free Hdbf.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_with_busy_prefix
    with (codec := codec)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec);
    eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
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
    feasible_schedule_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 sched.
Proof.
  intros T tasks offset H enumT enumJ jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched
         Hjob_bridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  destruct (Hjob_bridge j Hj) as
      [Hj_H [t1 [t2 [Hwit [Ht1rel Hcarry_free]]]]].
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon; eauto.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon_auto :
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
    feasible_schedule_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 sched.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  eapply periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon
    with (codec := codec)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec);
    eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon_with_busy_prefix :
  forall T tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
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
    feasible_schedule_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 sched.
Proof.
  intros T tasks offset H enumT enumJ jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched
         Hjob_bridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  destruct (Hjob_bridge j Hj) as
      [Hj_H [t1 [t2 [Hwit [Ht1rel Hcarry_free]]]]].
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_with_busy_prefix; eauto.
Qed.

Theorem periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon_auto_with_busy_prefix :
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
    feasible_schedule_on (periodic_jobset_upto T tasks offset jobs H) jobs 1 sched.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  eapply periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon_with_busy_prefix
    with (codec := codec)
         (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec);
    eauto using enum_periodic_jobs_upto_complete, enum_periodic_jobs_upto_sound.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon :
  forall T T_bool tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    (forall τ, T_bool τ = true <-> T τ) ->
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
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
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumT enumJ jobs codec sched
         HTbool Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched Hjob_bridge Hdbf.
  assert (Hfeas :
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1).
  {
    exists sched.
    split.
    - eapply single_cpu_algorithm_valid. exact Hsched.
    - eapply periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon; eauto.
  }
  eapply periodic_edf_optimality_on_finite_horizon; eauto.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto :
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
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  pose proof
    (periodic_window_dbf_implies_edf_feasible_on_finite_horizon
       T tasks offset H enumT jobs codec sched
       Hwf HnodupT HenumT_complete HenumT_sound
       Hsched Hjob_bridge Hdbf) as Hfeas.
  eapply periodic_edf_optimality_on_finite_horizon_auto; eauto.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_with_busy_prefix :
  forall T T_bool tasks offset H enumT enumJ jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         sched,
    (forall τ, T_bool τ = true <-> T τ) ->
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall x, periodic_jobset_upto T tasks offset jobs H x -> In x enumJ) ->
    (forall x, In x enumJ -> periodic_jobset_upto T tasks offset jobs H x) ->
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched ->
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
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler (enum_candidates_of enumJ))
      jobs 1.
Proof.
  intros T T_bool tasks offset H enumT enumJ jobs codec sched
         HTbool Hwf HnodupT HenumT_complete HenumT_sound
         HenumJ_complete HenumJ_sound Hsched Hjob_bridge Hdbf.
  assert (Hfeas :
    feasible_on (periodic_jobset_upto T tasks offset jobs H) jobs 1).
  {
    exists sched.
    split.
    - eapply single_cpu_algorithm_valid. exact Hsched.
    - eapply periodic_edf_feasible_schedule_from_window_dbf_on_finite_horizon_with_busy_prefix; eauto.
  }
  eapply periodic_edf_optimality_on_finite_horizon; eauto.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto_with_busy_prefix :
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
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec sched
         Hwf HnodupT HenumT_complete HenumT_sound
         Hsched Hjob_bridge Hdbf.
  pose proof
    (periodic_window_dbf_implies_edf_feasible_on_finite_horizon_with_busy_prefix
       T tasks offset H enumT jobs codec sched
       Hwf HnodupT HenumT_complete HenumT_sound
       Hsched Hjob_bridge Hdbf) as Hfeas.
  eapply periodic_edf_optimality_on_finite_horizon_auto; eauto.
Qed.

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_busy_prefix :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      (forall t1 t2,
        busy_prefix_witness
          (generated_schedule
             edf_generic_spec
             (enum_candidates_of
                (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
             jobs)
          (job_abs_deadline (jobs j)) t1 t2 ->
        t1 <= job_release (jobs j)) /\
      (forall t1 t2,
        busy_prefix_witness
          (generated_schedule
             edf_generic_spec
             (enum_candidates_of
                (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
             jobs)
          (job_abs_deadline (jobs j)) t1 t2 ->
        t1 <= job_release (jobs j) ->
        forall t j_run,
          job_release (jobs j) <= t < job_abs_deadline (jobs j) ->
          generated_schedule
            edf_generic_spec
            (enum_candidates_of
               (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))
            jobs t 0 = Some j_run ->
          periodic_jobset_deadline_between T tasks offset jobs
            t1 (job_abs_deadline (jobs j)) j_run ->
          job_release (jobs j) <= job_release (jobs j_run))) ->
    (forall t1 t2,
      t1 <= t2 ->
      t2 <= H ->
      taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec
         Hwf HnodupT HenumT_complete HenumT_sound
         Hjob_bridge Hdbf.
  set (enumJ := enum_periodic_jobs_upto T tasks offset jobs H enumT codec).
  set (sched := generated_schedule edf_generic_spec (enum_candidates_of enumJ) jobs).
  assert (Hcand_spec :
    CandidateSourceSpec (periodic_jobset_upto T tasks offset jobs H)
      (enum_candidates_of enumJ)).
  { apply enum_candidates_spec.
    - exact (enum_periodic_jobs_upto_complete T tasks offset jobs H enumT codec
               Hwf HenumT_complete).
    - exact (enum_periodic_jobs_upto_sound T tasks offset jobs H enumT codec
               HenumT_sound).
  }
  assert (Hsched :
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs 1 sched).
  {
    unfold sched.
    eapply generated_schedule_scheduler_rel with
      (J := periodic_jobset_upto T tasks offset jobs H)
      (cand_spec := Hcand_spec).
    intros s1 s2 t Hagree.
    eapply edf_choose_agrees_before; eauto.
  }
  eapply schedulable_by_on_intro with (sched := sched).
  - exact Hsched.
  - eapply single_cpu_algorithm_valid. exact Hsched.
  - intros j Hj.
    destruct (Hjob_bridge j Hj) as [Hj_H [Hstart_before_release Hcarry_free]].
    eapply periodic_window_dbf_implies_no_deadline_miss_under_generated_edf_with_busy_prefix; eauto.
Qed.
