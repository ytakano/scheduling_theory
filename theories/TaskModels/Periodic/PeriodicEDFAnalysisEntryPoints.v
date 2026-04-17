From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Export Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Export Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Export TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Export TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Export TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFClassicalBridge.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFPrefixCoherence.
From RocqSched Require Export TaskModels.Periodic.PeriodicEDFInfiniteBridge.

(** * Stable public entry points for idealized periodic EDF analysis

    This file is the canonical downstream import for the current
    periodic EDF processor-demand / busy-prefix theorem layer.

    Public theorem families exposed here:
    - busy-prefix witness search facts
    - EDF processor-demand bridge facts
    - periodic window-DBF bridge facts
    - infinite-time periodic EDF candidate/coherence interfaces
    - infinite-time generated-EDF no-miss / feasible wrappers
      over the weaker no-carry-in bridge interface
    - `periodic_edf_schedulable_by_on` as the canonical infinite-time
      window-DBF schedulability API
    - `periodic_edf_schedulable_by_classical_dbf_on` as the explicit
      zero-offset classical-DBF convenience wrapper
    - `periodic_edf_schedulable_by_window_dbf_on` as the explicit
      window-DBF alias
    - bounded finite-horizon concrete DBF/window-DBF checkers
    - scalar cutoff helpers for infinite zero-offset classical DBF proofs
    - finite- and infinite-time zero-offset classical-DBF corollaries with
      explicit busy-prefix or no-carry-in bridges
    - periodic EDF no-miss / feasible-schedule / schedulable-by-on wrappers
    - finite generated-EDF wrappers that internalize
      `start_before_release` and keep only
      `periodic_edf_busy_prefix_no_carry_in_bridge` public,
      with downstream concrete proofs expected to use local idle-slot facts
      whenever they can avoid full busy-prefix case splits

    Not part of this layer:
    - legacy compatibility wrappers
    - unpackaged busy-prefix interfaces
    - generated-EDF auto-derivation of `no_carry_in`
    - future sporadic / jittered generalizations
    - delay-aware or OS-operational analysis *)

Theorem periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations :
  forall T tasks offset H enumT jobs
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    PeriodicEDFConcreteWindowObligations T tasks offset jobs H enumT codec ->
    schedulable_by_on
      (periodic_jobset_upto T tasks offset jobs H)
      (edf_scheduler
         (enum_candidates_of
            (generated_periodic_edf_finite_enumJ T tasks offset jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks offset H enumT jobs codec Hobl.
  destruct Hobl as
      [Hwf HnodupT HenumT_complete HenumT_sound Hjob_bridge Hwindow_test].
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_no_carry_in_bridge.
  - exact Hwf.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Hjob_bridge.
  - intros t1 t2 Hle12 Hle2H.
    eapply window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_on_finite_horizon_generated_from_obligations :
  forall T tasks jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks (fun _ => 0) jobs H),
    PeriodicEDFConcreteClassicalObligations T tasks jobs H enumT codec ->
    schedulable_by_on
      (periodic_jobset_upto T tasks (fun _ => 0) jobs H)
      (edf_scheduler
         (enum_candidates_of
            (generated_periodic_edf_finite_enumJ
               T tasks (fun _ => 0) jobs H enumT codec)))
      jobs 1.
Proof.
  intros T tasks jobs H enumT codec Hobl.
  destruct Hobl as [Hwindow Hdbf_test].
  destruct Hwindow as
      [Hwf HnodupT HenumT_complete HenumT_sound Hjob_bridge Hwindow_test].
  eapply periodic_classical_dbf_implies_generated_edf_schedulable_with_no_carry_in_bridge.
  - exact Hwf.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - intros τ Hin. reflexivity.
  - eapply dbf_check_by_cutoff.
    + exact HnodupT.
    + intros τ Hin.
      apply Hwf.
      apply HenumT_sound.
      exact Hin.
    + exact Hdbf_test.
  - exact Hjob_bridge.
Qed.

Theorem periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    PeriodicEDFConcreteInfiniteClassicalObligations
      T tasks offset jobs enumT codec ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler
         (periodic_candidates_before
            T tasks offset jobs enumT codec))
      jobs 1.
Proof.
  intros T tasks offset jobs enumT codec Hobl.
  destruct Hobl as
      [Hwf HnodupT HenumT_complete HenumT_sound Hoff Hjob_bridge Hdbf_test].
  eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge.
  - exact Hwf.
  - exact HnodupT.
  - exact HenumT_complete.
  - exact HenumT_sound.
  - exact Hoff.
  - exact Hjob_bridge.
  - eapply dbf_check_by_cutoff.
    + exact HnodupT.
    + intros τ Hin.
      apply Hwf.
      apply HenumT_sound.
      exact Hin.
    + exact Hdbf_test.
Qed.
