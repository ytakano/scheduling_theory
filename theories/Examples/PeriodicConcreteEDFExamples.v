From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFAnalysisEntryPoints.
From RocqSched Require Import Examples.PeriodicExamples.
From RocqSched Require Import Examples.PeriodicProcessorDemandExamples.

Import ListNotations.

Example periodic_concrete_dbf_test_upto_ex :
  dbf_test_upto tasks_ex enumT_ex H_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example periodic_concrete_window_dbf_test_upto_ex :
  window_dbf_test_upto tasks_ex offset_ex enumT_ex H_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_concrete_bounded_dbf_ex :
  forall t,
    t <= H_ex ->
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  intros t Hle.
  eapply (dbf_test_upto_true_implies_bounded_dbf tasks_ex enumT_ex H_ex t).
  - exact periodic_concrete_dbf_test_upto_ex.
  - exact Hle.
Qed.

Lemma periodic_concrete_bounded_window_dbf_ex :
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H_ex ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  intros t1 t2 Hle12 Hle2H.
  eapply (window_dbf_test_upto_true_implies_bounded_window_dbf
            tasks_ex offset_ex enumT_ex H_ex t1 t2).
  - exact periodic_concrete_window_dbf_test_upto_ex.
  - exact Hle12.
  - exact Hle2H.
Qed.

Example periodic_concrete_dbf_at_horizon_ex :
  taskset_periodic_dbf tasks_ex enumT_ex H_ex <= H_ex.
Proof.
  apply periodic_concrete_bounded_dbf_ex.
  unfold H_ex.
  lia.
Qed.

Theorem periodic_concrete_edf_schedulable_by_window_checker_generated_with_busy_prefix_bridge :
  (forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    job_abs_deadline (jobs_ex j) <= H_ex /\
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex H_ex
      (generated_schedule
         edf_generic_spec
         (enum_candidates_of
            (enum_periodic_jobs_upto
               T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex))
         jobs_ex)
      j) ->
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (edf_scheduler
       (enum_candidates_of
          (enum_periodic_jobs_upto
             T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
    jobs_ex 1.
Proof.
  intro Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_busy_prefix_bridge
    with (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - exact T_ex_in_enumT_ex.
  - exact in_enumT_ex_implies_T_ex.
  - exact periodic_concrete_bounded_window_dbf_ex.
Qed.

Theorem periodic_concrete_llf_schedulable_by_window_checker_generated_with_busy_prefix_bridge :
  (forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    job_abs_deadline (jobs_ex j) <= H_ex /\
    exists t1 t2,
      busy_prefix_witness
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto
                 T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex))
           jobs_ex)
        (job_abs_deadline (jobs_ex j)) t1 t2 /\
      periodic_edf_busy_prefix_bridge
        T_ex tasks_ex offset_ex jobs_ex H_ex
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto
                 T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex))
           jobs_ex)
        j) ->
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (llf_scheduler
       (enum_candidates_of
          (enum_periodic_jobs_upto
             T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
    jobs_ex 1.
Proof.
  intro Hjob_bridge.
  set (enumJ :=
         enum_periodic_jobs_upto
           T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex).
  set (sched := generated_schedule edf_generic_spec (enum_candidates_of enumJ) jobs_ex).
  assert (Hcand_spec :
    CandidateSourceSpec (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (enum_candidates_of enumJ)).
  {
    apply enum_candidates_spec.
    - exact (enum_periodic_jobs_upto_complete
               T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex
               tasks_ex_well_formed
               T_ex_in_enumT_ex).
    - exact (enum_periodic_jobs_upto_sound
               T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex
               in_enumT_ex_implies_T_ex).
  }
  assert (Hsched :
    scheduler_rel (edf_scheduler (enum_candidates_of enumJ)) jobs_ex 1 sched).
  {
    unfold sched.
    eapply generated_schedule_scheduler_rel with
      (J := periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (cand_spec := Hcand_spec).
    intros s1 s2 t Hagree.
    eapply edf_choose_agrees_before; eauto.
  }
  eapply periodic_llf_schedulable_by_window_dbf_on_finite_horizon_auto_with_busy_prefix_bridge
    with (enumT := enumT_ex) (sched := sched); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - exact T_ex_in_enumT_ex.
  - exact in_enumT_ex_implies_T_ex.
  - exact periodic_concrete_bounded_window_dbf_ex.
Qed.
