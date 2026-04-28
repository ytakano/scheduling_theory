From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Policies.LLFOptimality.
From RocqSched Require Import Uniprocessor.Policies.LLFLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteOptimalityLift.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicLLFPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFInfiniteBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFPrefixCoherence.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFWindowBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicLLFBridge.

Theorem jittered_periodic_llf_no_deadline_miss_from_window_dbf :
  forall T tasks offset jitter enumT jobs
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j_block t,
      jittered_periodic_jobset T tasks offset jitter jobs j_block ->
      ~ blocked jobs j_block t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall H j_ref,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j_ref ->
      job_abs_deadline (jobs j_ref) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_jittered_periodic_edf_schedule_upto
           T tasks offset jitter jobs
           H enumT codec)
        j_ref) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    (forall j_miss,
      jittered_periodic_jobset T tasks offset jitter jobs j_miss ->
      ~ missed_deadline jobs 1
        (generated_jittered_periodic_llf_schedule
           T tasks offset jitter jobs enumT codec) j_miss).
Proof.
  intros T tasks offset jitter enumT jobs codec
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf j Hjob.
  set (HH := S (job_abs_deadline (jobs j))).
  set (sched_fin :=
    generated_jittered_periodic_llf_schedule_upto
      T tasks offset jitter jobs HH enumT codec).
  set (sched_inf :=
    generated_jittered_periodic_llf_schedule
      T tasks offset jitter jobs enumT codec).
  assert (Hjob_upto :
    jittered_periodic_jobset_upto T tasks offset jitter jobs HH j).
  {
    unfold HH.
    apply jittered_periodic_jobset_with_release_lt_implies_upto.
    - exact Hjob.
    - pose proof (jittered_periodic_jobset_implies_generated
                   T tasks offset jitter jobs j Hjob) as Hgen.
      pose proof (generated_by_jittered_periodic_deadline_eq
                   tasks offset jitter jobs j Hgen) as Hdl.
      lia.
  }
  assert (Hfeasible :
    feasible_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs HH)
      jobs 1).
  {
    unfold HH.
    eapply
      jittered_window_dbf_implies_edf_feasible_on_finite_horizon_with_no_carry_in_bridge
      with
      (codec :=
         jittered_periodic_finite_horizon_codec_of
           T tasks offset jitter jobs HH codec).
    - exact Hwf.
    - intros j' t Hj.
      apply Hnonblocked.
      exact (jittered_periodic_jobset_upto_implies_jittered_periodic_jobset
               T tasks offset jitter jobs HH j' Hj).
    - exact HnodupT.
    - exact HenumT_complete.
    - exact HenumT_sound.
    - intros j' Hj'.
      exact (Hbridge HH j' Hj').
    - intros t1 t2 Hle1 Hle2.
      exact (Hdbf t1 t2 Hle1).
  }
  assert (Hllf_fin_schedulable :
    schedulable_by_on
      (jittered_periodic_jobset_upto T tasks offset jitter jobs HH)
      (llf_scheduler
         (enum_candidates_of
            (enum_jittered_periodic_jobs_upto
               T tasks offset jitter jobs HH enumT
               (jittered_periodic_finite_horizon_codec_of
                  T tasks offset jitter jobs HH codec))))
      jobs 1).
  {
    eapply jittered_periodic_finite_optimality_lift
      with
      (local_scheduler := llf_scheduler)
      (Hoptimal := llf_optimality_on_finite_jobs)
      (T := T)
      (T_bool := task_in_list_b enumT)
      (tasks := tasks)
      (offset := offset)
      (jitter := jitter)
      (H := HH)
      (enumJ := enum_jittered_periodic_jobs_upto
                  T tasks offset jitter jobs HH enumT
                  (jittered_periodic_finite_horizon_codec_of
                     T tasks offset jitter jobs HH codec))
      (jobs := jobs).
    - intros τ.
      rewrite task_in_list_b_spec.
      split; [apply HenumT_sound | apply HenumT_complete].
    - intros j_block t Hj_block.
      apply Hnonblocked with (t := t) (j_block := j_block).
      exact (jittered_periodic_jobset_upto_implies_jittered_periodic_jobset
               T tasks offset jitter jobs HH j_block Hj_block).
    - intros j' Hj';
      exact (enum_jittered_periodic_jobs_upto_complete
               T tasks offset jitter jobs HH enumT
               (jittered_periodic_finite_horizon_codec_of
                  T tasks offset jitter jobs HH codec)
               Hwf HenumT_complete j' Hj').
    - intros j' Hj';
      exact (enum_jittered_periodic_jobs_upto_sound
               T tasks offset jitter jobs HH enumT
               (jittered_periodic_finite_horizon_codec_of
                  T tasks offset jitter jobs HH codec)
               HenumT_sound j' Hj').
    - exact Hfeasible.
  }
  assert (Hfin_feasible : feasible_schedule_on
    (jittered_periodic_jobset_upto T tasks offset jitter jobs HH)
    jobs 1 sched_fin).
  {
    unfold sched_fin, generated_jittered_periodic_llf_schedule_upto.
    eapply schedulable_by_on_implies_generated_schedule_feasible.
    - intros s1 s2 t Hagree.
      exact
        (llf_choose_agrees_before
          (jittered_periodic_jobset_upto T tasks offset jitter jobs HH)
           (enum_candidates_of
             (enum_jittered_periodic_jobs_upto
                T tasks offset jitter jobs HH enumT
                (jittered_periodic_finite_horizon_codec_of
                   T tasks offset jitter jobs HH codec)))
           (enum_candidates_spec
              (jittered_periodic_jobset_upto
                 T tasks offset jitter jobs HH)
              (enum_jittered_periodic_jobs_upto
                 T tasks offset jitter jobs HH enumT
                 (jittered_periodic_finite_horizon_codec_of
                    T tasks offset jitter jobs HH codec))
              (enum_jittered_periodic_jobs_upto_complete
                 T tasks offset jitter jobs HH enumT
                 (jittered_periodic_finite_horizon_codec_of
                    T tasks offset jitter jobs HH codec)
                 Hwf HenumT_complete)
              (enum_jittered_periodic_jobs_upto_sound
                 T tasks offset jitter jobs HH enumT
                 (jittered_periodic_finite_horizon_codec_of
                    T tasks offset jitter jobs HH codec)
                 HenumT_sound))
           jobs s1 s2 t Hagree).
    - exact Hllf_fin_schedulable.
  }
  assert (Hfin_no_miss :
    ~ missed_deadline jobs 1 sched_fin j).
  {
    apply Hfin_feasible.
    exact Hjob_upto.
  }
  unfold missed_deadline in *.
  intro Hmiss_inf.
  assert (Hagree_deadline :
    agrees_before sched_fin sched_inf (job_abs_deadline (jobs j))).
  {
    eapply (agrees_before_weaken sched_fin sched_inf
                                  (job_abs_deadline (jobs j)) HH).
    - unfold HH. lia.
    - unfold sched_fin, sched_inf.
      eapply infinite_generated_jittered_llf_prefix_coherence; eauto.
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

Theorem jittered_periodic_llf_feasible_schedule_from_window_dbf :
  forall T tasks offset jitter enumT jobs
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j_block t,
      jittered_periodic_jobset T tasks offset jitter jobs j_block ->
      ~ blocked jobs j_block t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall H j_ref,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j_ref ->
      job_abs_deadline (jobs j_ref) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_jittered_periodic_edf_schedule_upto
           T tasks offset jitter jobs
           H enumT codec)
        j_ref) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    feasible_schedule_on
      (jittered_periodic_jobset T tasks offset jitter jobs)
      jobs 1
      (generated_jittered_periodic_llf_schedule
         T tasks offset jitter jobs enumT codec).
Proof.
  intros T tasks offset jitter enumT jobs codec
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  unfold feasible_schedule_on.
  intros j Hj.
  eapply jittered_periodic_llf_no_deadline_miss_from_window_dbf; eauto.
Qed.

Theorem jittered_periodic_llf_schedulable_by_window_dbf_on :
  forall T tasks offset jitter enumT jobs
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall j_block t,
      jittered_periodic_jobset T tasks offset jitter jobs j_block ->
      ~ blocked jobs j_block t) ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall H j_ref,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j_ref ->
      job_abs_deadline (jobs j_ref) <= H /\
      jittered_periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jitter jobs H
        (generated_jittered_periodic_edf_schedule_upto
           T tasks offset jitter jobs
           H enumT codec)
        j_ref) ->
    (forall t1 t2,
      t1 <= t2 ->
      taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 <=
      t2 - t1) ->
    schedulable_by_on
      (jittered_periodic_jobset T tasks offset jitter jobs)
      (llf_scheduler
         (jittered_periodic_candidates_before T tasks offset jitter jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset jitter enumT jobs codec
         Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound
         Hbridge Hdbf.
  eapply schedulable_by_on_intro with
    (sched := generated_jittered_periodic_llf_schedule
                T tasks offset jitter jobs enumT codec).
  - exact (infinite_generated_jittered_llf_scheduler_rel T tasks offset jitter
             jobs enumT codec).
  - unfold generated_jittered_periodic_llf_schedule.
    eapply single_cpu_algorithm_valid.
    exact (infinite_generated_jittered_llf_scheduler_rel
             T tasks offset jitter jobs enumT codec).
  - exact (jittered_periodic_llf_feasible_schedule_from_window_dbf
            T tasks offset jitter enumT jobs codec
            Hwf Hnonblocked HnodupT HenumT_complete HenumT_sound Hbridge Hdbf).
Qed.
