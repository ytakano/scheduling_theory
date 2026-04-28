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
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFWindowBridge.

Definition generated_jittered_periodic_edf_schedule
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : JitteredPeriodicCodec T tasks offset jitter jobs) : Schedule :=
  generated_schedule
    edf_generic_spec
    (jittered_periodic_candidates_before T tasks offset jitter jobs enumT codec)
    jobs.

Definition generated_jittered_periodic_edf_schedule_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : JitteredPeriodicCodec T tasks offset jitter jobs) : Schedule :=
  generated_schedule
    edf_generic_spec
    (enum_candidates_of
       (enum_jittered_periodic_jobs_upto
          T tasks offset jitter jobs H enumT
          (jittered_periodic_finite_horizon_codec_of
             T tasks offset jitter jobs H codec)))
    jobs.

Lemma infinite_generated_jittered_edf_scheduler_rel :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    scheduler_rel
      (edf_scheduler
         (jittered_periodic_candidates_before
            T tasks offset jitter jobs enumT codec))
      jobs 1
      (generated_jittered_periodic_edf_schedule
         T tasks offset jitter jobs enumT codec).
Proof.
  intros T tasks offset jitter jobs enumT codec.
  unfold generated_jittered_periodic_edf_schedule,
         edf_scheduler, single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + rewrite generated_schedule_eq_cpu0_with_prefix.
      simpl.
      rewrite
        (choose_edf_agrees_before
           jobs
           (generated_schedule_prefix
              edf_generic_spec
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec)
              jobs t)
           (generated_schedule
              edf_generic_spec
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec)
              jobs)
           t
           (jittered_periodic_candidates_before
              T tasks offset jitter jobs enumT codec jobs 1
              (generated_schedule_prefix
                 edf_generic_spec
                 (jittered_periodic_candidates_before
                    T tasks offset jitter jobs enumT codec)
                 jobs t) t)
           (generated_schedule_prefix_agrees_before
              edf_generic_spec
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec)
              jobs t)).
      rewrite
        (jittered_periodic_candidates_before_prefix_extensional
           T tasks offset jitter jobs enumT codec jobs 1
           (generated_schedule_prefix
              edf_generic_spec
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec)
              jobs t)
           (generated_schedule
              edf_generic_spec
              (jittered_periodic_candidates_before
                 T tasks offset jitter jobs enumT codec)
              jobs)
           t).
      reflexivity.
    + intros c Hc.
      apply generated_schedule_other_cpu_idle.
      exact Hc.
Qed.

Lemma generated_jittered_periodic_edf_schedule_valid :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    valid_schedule jobs 1
      (generated_jittered_periodic_edf_schedule
         T tasks offset jitter jobs enumT codec).
Proof.
  intros T tasks offset jitter jobs enumT codec.
  eapply single_cpu_algorithm_valid.
  apply infinite_generated_jittered_edf_scheduler_rel.
Qed.

Theorem jittered_periodic_edf_schedulable_by_window_dbf_on :
  forall T tasks offset jitter enumT jobs
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j t,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      ~ blocked jobs j t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall j,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs (S (job_abs_deadline (jobs j)))
        (generated_jittered_periodic_edf_schedule_upto
           T tasks offset jitter jobs
           (S (job_abs_deadline (jobs j))) enumT codec)
        j) ->
    (forall j,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      agrees_before
        (generated_jittered_periodic_edf_schedule_upto
           T tasks offset jitter jobs
           (S (job_abs_deadline (jobs j))) enumT codec)
        (generated_jittered_periodic_edf_schedule
           T tasks offset jitter jobs enumT codec)
        (job_abs_deadline (jobs j))) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    schedulable_by_on
      (jittered_periodic_jobset T tasks offset jitter jobs)
      (edf_scheduler
         (jittered_periodic_candidates_before
            T tasks offset jitter jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset jitter enumT jobs codec
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hbridge Hagree Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_jittered_periodic_edf_schedule
                T tasks offset jitter jobs enumT codec).
  - apply infinite_generated_jittered_edf_scheduler_rel.
  - apply generated_jittered_periodic_edf_schedule_valid.
  - unfold feasible_schedule_on.
    intros j Hj Hmiss_inf.
    set (HH := S (job_abs_deadline (jobs j))).
    set (sched_fin :=
      generated_jittered_periodic_edf_schedule_upto
        T tasks offset jitter jobs HH enumT codec).
    assert (Hjob_upto :
      jittered_periodic_jobset_upto T tasks offset jitter jobs HH j).
    {
      unfold HH.
      apply jittered_periodic_jobset_with_release_lt_implies_upto.
      - exact Hj.
      - pose proof (jittered_periodic_jobset_implies_generated
                      T tasks offset jitter jobs j Hj) as Hgen.
        pose proof (generated_by_jittered_periodic_deadline_eq
                      tasks offset jitter jobs j Hgen) as Hdl.
        lia.
    }
    assert (Hfin_no_miss :
      ~ missed_deadline jobs 1 sched_fin j).
    {
      unfold sched_fin, generated_jittered_periodic_edf_schedule_upto, HH.
      eapply jittered_window_dbf_implies_no_deadline_miss_under_generated_edf_with_no_carry_in_bridge.
      - exact Hwf.
      - intros j' t Hj'.
        apply Hnonblocked.
        exact (jittered_periodic_jobset_upto_implies_jittered_periodic_jobset
                 T tasks offset jitter jobs (S (job_abs_deadline (jobs j))) j' Hj').
      - exact HnodupT.
      - exact HenumT_complete.
      - exact HenumT_sound.
      - exact Hjob_upto.
      - lia.
      - exact (Hbridge j Hj).
      - intros t1 t2 Hle _.
        exact (Hdbf t1 t2 Hle).
    }
    apply Hfin_no_miss.
    unfold missed_deadline in *.
    intro Hcomp_fin.
    apply Hmiss_inf.
    destruct (agrees_before_completed
                jobs 1 sched_fin
                (generated_jittered_periodic_edf_schedule
                   T tasks offset jitter jobs enumT codec)
                j (job_abs_deadline (jobs j))
                (Hagree j Hj)) as [Hcomp_inf _].
    exact (Hcomp_inf Hcomp_fin).
Qed.
