From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
From RocqSched Require Export TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFAnalysisBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFPrefixCoherence.
From RocqSched Require Export TaskModels.Periodic.PeriodicLLFInfiniteBridge.

(** * Stable public entry points for idealized periodic LLF analysis

    This file is the canonical downstream import for the current
    periodic LLF schedulability-analysis wrapper layer.

    Public theorem families exposed here:
    - the packaged periodic EDF idealized-analysis inventory
    - periodic LLF finite-horizon optimality wrappers
    - finite concrete window-DBF package wrapper for generated LLF,
      keeping the busy-prefix bridge premise explicit
    - `periodic_llf_schedulable_by_on` as the canonical infinite-time
      window-DBF schedulability API
    - `periodic_llf_schedulable_by_classical_dbf_on` as the explicit
      zero-offset classical-DBF convenience wrapper
    - `periodic_llf_schedulable_by_window_dbf_on` as the explicit
      window-DBF alias
    - bounded finite-horizon concrete DBF/window-DBF checkers
    - scalar cutoff helpers for infinite zero-offset classical DBF proofs
    - infinite-time periodic LLF candidate/coherence interfaces
    - infinite-time generated-LLF no-miss / feasible / schedulable wrappers
    - infinite-time zero-offset classical-DBF corollaries
    - explicit bridge-first APIs that keep
      `periodic_edf_busy_prefix_bridge` in the public assumptions

    Not part of this layer:
    - legacy compatibility wrappers
    - weakened APIs that auto-supply `no_carry_in`
    - future sporadic / jittered / delay-aware analysis wrappers *)

Theorem periodic_llf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    PeriodicEDFConcreteWindowObligations T tasks offset jobs H enumT codec ->
    (forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      exists t1 t2,
        busy_prefix_witness
          (generated_periodic_edf_schedule_on_finite_horizon
             T tasks offset jobs H enumT codec)
          (job_abs_deadline (jobs j)) t1 t2 /\
        periodic_edf_busy_prefix_bridge
          T tasks offset jobs H
          (generated_periodic_edf_schedule_on_finite_horizon
             T tasks offset jobs H enumT codec)
          j) ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (llf_scheduler
         (enum_candidates_of
            (generated_periodic_edf_finite_enumJ T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec Hobl Hbusy_bridge.
  destruct Hobl as
      [Hwf HnodupT HenumT_complete HenumT_sound Hnonblocked _Hno_carry Hwindow_test].
  pose proof (enum_candidates_spec
        (periodic_jobset_upto T tasks offset jobs H)
        (generated_periodic_edf_finite_enumJ T tasks offset jobs H enumT codec)
        (enum_periodic_jobs_upto_complete
           T tasks offset jobs H enumT codec Hwf HenumT_complete)
        (enum_periodic_jobs_upto_sound
           T tasks offset jobs H enumT codec HenumT_sound)) as Hcand_spec.
  eapply periodic_llf_schedulable_by_window_dbf_on_finite_horizon_auto_with_busy_prefix_bridge
    with (sched := generated_periodic_edf_schedule_on_finite_horizon
                    T tasks offset jobs H enumT codec).
  - exact Hwf.
  - exact Hnonblocked.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - unfold generated_periodic_edf_schedule_on_finite_horizon.
    eapply
      (generated_schedule_scheduler_rel
         edf_generic_spec
         (periodic_jobset_upto T tasks offset jobs H)
         (enum_candidates_of
            (generated_periodic_edf_finite_enumJ
               T tasks offset jobs H enumT codec))
         Hcand_spec
         jobs).
    intros s1 s2 t Hagree.
    exact (edf_choose_agrees_before
             (periodic_jobset_upto T tasks offset jobs H)
             (enum_candidates_of
                (generated_periodic_edf_finite_enumJ
                   T tasks offset jobs H enumT codec))
             Hcand_spec jobs s1 s2 t Hagree).
  - exact Hbusy_bridge.
  - intros t1 t2 Hle12 Hle2H.
    eapply window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.
