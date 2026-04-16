From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Policies.LLFLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.
Import ListNotations.

Lemma generated_schedule_prefix_coherent_at_llf :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) H,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall h t c,
      t < h ->
      h <= H ->
      generated_schedule_prefix
        llf_generic_spec
        (enum_candidates_of
           (enum_periodic_jobs_upto
              T tasks offset jobs H enumT
              (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
        jobs h t c =
      generated_schedule_prefix
        llf_generic_spec
        (periodic_candidates_before T tasks offset jobs enumT codec)
        jobs h t c.
Proof.
  intros T tasks offset jobs enumT codec H Hwf HenumT_complete HenumT_sound h.
  induction h as [|h' IH]; intros t c Hlt Hh.
  - lia.
  - simpl.
    destruct (Nat.eq_dec t h') as [Heq|Hneq].
    + subst t.
      destruct c as [|c'].
      * rewrite Nat.eqb_refl.
        simpl.
        rewrite Nat.ltb_irrefl.
        change
          (choose llf_generic_spec jobs 1
             (generated_schedule_prefix
                llf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
          with
          (choose_llf jobs 1
             (generated_schedule_prefix
                llf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec))).
        change
          (choose llf_generic_spec jobs 1
             (generated_schedule_prefix
                llf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                (generated_schedule_prefix
                   llf_generic_spec
                   (periodic_candidates_before T tasks offset jobs enumT codec)
                   jobs h') h'))
          with
          (choose_llf jobs 1
             (generated_schedule_prefix
                llf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                (generated_schedule_prefix
                   llf_generic_spec
                   (periodic_candidates_before T tasks offset jobs enumT codec)
                   jobs h') h')).
        assert (Hagree :
          agrees_before
            (generated_schedule_prefix
               llf_generic_spec
               (enum_candidates_of
                  (enum_periodic_jobs_upto
                     T tasks offset jobs H enumT
                     (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
               jobs h')
            (generated_schedule_prefix
               llf_generic_spec
               (periodic_candidates_before T tasks offset jobs enumT codec)
               jobs h')
            h').
        {
          intros t' c' Hlt'.
          apply IH; try assumption; lia.
        }
        transitivity
          (choose_llf jobs 1
             (generated_schedule_prefix
                llf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec))).
        2: {
          rewrite choose_llf_filter_ineligible
            with (keep := fun j => Nat.ltb (job_release (jobs j)) (S h')).
          - replace
              (filter (fun j : JobId => job_release (jobs j) <? S h')
                 (enum_periodic_jobs_upto T tasks offset jobs H enumT
                    (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
              with (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                      (generated_schedule_prefix
                         llf_generic_spec
                         (periodic_candidates_before T tasks offset jobs enumT codec)
                         jobs h') h').
            2: {
              rewrite (enum_periodic_jobs_upto_filter_before
                         T tasks offset jobs H enumT codec h'
                         Hwf HenumT_sound).
              2: lia.
              unfold periodic_candidates_before.
              reflexivity.
            }
            unfold periodic_candidates_before.
            reflexivity.
          - intros j Hin Hkeep.
            eapply future_job_not_eligible_at_time; eauto.
        }
        apply choose_llf_agrees_before.
        exact Hagree.
      * rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        simpl.
        destruct (Nat.eqb_spec (S c') 0); [lia | reflexivity].
    + assert (t < h') by lia.
      destruct (Nat.ltb t h') eqn:Hcmp.
      * apply IH; try assumption; lia.
      * apply Nat.ltb_ge in Hcmp.
        lia.
Qed.

Theorem infinite_generated_llf_prefix_coherence :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall H,
      agrees_before
        (generated_schedule
           llf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto
                 T tasks offset jobs H enumT
                 (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
           jobs)
        (generated_schedule
           llf_generic_spec
           (periodic_candidates_before T tasks offset jobs enumT codec)
           jobs)
        H.
Proof.
  intros T tasks offset jobs enumT codec Hwf HenumT_complete HenumT_sound H t c Hlt.
  rewrite <- (generated_schedule_prefix_stable
                llf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs H t c Hlt).
  rewrite <- (generated_schedule_prefix_stable
                llf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs H t c Hlt).
  eapply generated_schedule_prefix_coherent_at_llf; eauto; lia.
Qed.

Lemma infinite_generated_llf_scheduler_rel :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    scheduler_rel
      (llf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1
      (generated_schedule
         llf_generic_spec
         (periodic_candidates_before T tasks offset jobs enumT codec)
         jobs).
Proof.
  intros T tasks offset jobs enumT codec.
  unfold llf_scheduler, single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + rewrite generated_schedule_eq_cpu0_with_prefix.
      change
        (choose llf_generic_spec jobs 1
           (generated_schedule_prefix
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs t)
           t
           (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
              (generated_schedule_prefix
                 llf_generic_spec
                 (periodic_candidates_before T tasks offset jobs enumT codec)
                 jobs t) t))
        with
        (choose_llf jobs 1
           (generated_schedule_prefix
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs t)
           t
           (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
              (generated_schedule_prefix
                 llf_generic_spec
                 (periodic_candidates_before T tasks offset jobs enumT codec)
                 jobs t) t)).
      change
        (choose llf_generic_spec jobs 1
           (generated_schedule
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs)
           t
           (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
              (generated_schedule
                 llf_generic_spec
                 (periodic_candidates_before T tasks offset jobs enumT codec)
                 jobs) t))
        with
        (choose_llf jobs 1
           (generated_schedule
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs)
           t
           (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
              (generated_schedule
                 llf_generic_spec
                 (periodic_candidates_before T tasks offset jobs enumT codec)
                 jobs) t)).
      rewrite (choose_llf_agrees_before
                 jobs
                 (generated_schedule_prefix
                    llf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs t)
                 (generated_schedule
                    llf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs)
                 t
                 (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                    (generated_schedule_prefix
                       llf_generic_spec
                       (periodic_candidates_before T tasks offset jobs enumT codec)
                       jobs t) t)
                 (generated_schedule_prefix_agrees_before
                    llf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs t)).
      rewrite
        (periodic_candidates_before_prefix_extensional
           T tasks offset jobs enumT codec jobs 1
           (generated_schedule_prefix
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs t)
           (generated_schedule
              llf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs)
           t).
      reflexivity.
    + intros c Hc.
      apply generated_schedule_other_cpu_idle.
      exact Hc.
Qed.
