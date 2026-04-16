From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFAnalysisEntryPoints.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Examples.PeriodicExamples.

Import ListNotations.

(* Canonical downstream client of the stable periodic EDF analysis entry point. *)

Example periodic_window_dbf_task0_ex :
  periodic_dbf_window tasks_ex offset_ex 0 0 4 = 2.
Proof. reflexivity. Qed.

Example periodic_window_dbf_task1_ex :
  periodic_dbf_window tasks_ex offset_ex 1 0 4 = 1.
Proof. reflexivity. Qed.

Example periodic_window_dbf_taskset_ex :
  taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex 0 4 = 3.
Proof. reflexivity. Qed.

Lemma periodic_window_dbf_test :
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H_ex ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  intros t1 t2 Hle1 Hle2.
  unfold H_ex in Hle2.
  assert (t1 <= 4) by lia.
  destruct t1 as [| [| [| [| [| t1']]]]]; try lia;
    destruct t2 as [| [| [| [| [| t2']]]]]; try lia;
    cbn in *; lia.
Qed.

Lemma enumT_ex_nodup :
  NoDup enumT_ex.
Proof.
  unfold enumT_ex.
  constructor.
  - simpl. intros [H | []]. discriminate.
  - constructor.
    + simpl. tauto.
    + constructor.
Qed.

Lemma T_ex_in_enumT_ex :
  forall τ, T_ex τ -> In τ enumT_ex.
Proof.
  intros τ Hτ.
  destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
Qed.

Lemma in_enumT_ex_implies_T_ex :
  forall τ, In τ enumT_ex -> T_ex τ.
Proof.
  intros τ Hτ.
  simpl in Hτ.
  destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem periodic_example_edf_no_deadline_miss_by_window_dbf_auto_with_busy_prefix_bridge :
  forall sched j t1 t2,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
    job_abs_deadline (jobs_ex j) <= H_ex ->
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex H_ex sched j ->
    ~ missed_deadline jobs_ex 1 sched j.
Proof.
  intros sched j t1 t2 Hsched Hj Hwit Hj_H Hbridge.
  eapply periodic_edf_no_deadline_miss_from_window_dbf_on_finite_horizon_auto_with_busy_prefix_bridge
    with (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Lemma periodic_example_edf_busy_prefix_bridge :
  forall sched j,
    (forall t1 t2,
      busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
      t1 <= job_release (jobs_ex j)) ->
    (forall t1 t2,
      busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 ->
      t1 <= job_release (jobs_ex j) ->
      forall t j_run,
        job_release (jobs_ex j) <= t < job_abs_deadline (jobs_ex j) ->
        sched t 0 = Some j_run ->
        periodic_jobset_deadline_between T_ex tasks_ex offset_ex jobs_ex
          t1 (job_abs_deadline (jobs_ex j)) j_run ->
        job_release (jobs_ex j) <= job_release (jobs_ex j_run)) ->
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex H_ex sched j.
Proof.
  intros sched j Hstart Hcarry.
  apply periodic_edf_busy_prefix_bridge_of_hypotheses; assumption.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_auto_with_busy_prefix_bridge :
  forall sched,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1 sched ->
    (forall j,
      periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
      job_abs_deadline (jobs_ex j) <= H_ex /\
      exists t1 t2,
        busy_prefix_witness sched (job_abs_deadline (jobs_ex j)) t1 t2 /\
        periodic_edf_busy_prefix_bridge
          T_ex tasks_ex offset_ex jobs_ex H_ex sched j) ->
    schedulable_by_on
      (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1.
Proof.
  intros sched Hsched Hjob_bridge.
  eapply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_auto_with_busy_prefix_bridge
    with (sched := sched) (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_edf_schedulable_by_window_dbf_generated_with_busy_prefix_bridge :
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
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_edf_schedulable_by_classical_dbf_generated_with_busy_prefix_bridge :
  (forall t, taskset_periodic_dbf tasks_ex enumT_ex t <= t) ->
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
  intros Hdbf_classical Hjob_bridge.
  eapply periodic_classical_dbf_implies_generated_edf_schedulable_with_busy_prefix_bridge
    with (enumT := enumT_ex); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
Qed.

Theorem periodic_example_llf_schedulable_by_window_dbf_generated_with_busy_prefix_bridge :
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
  - intros τ Hτ.
    exact (T_ex_in_enumT_ex τ Hτ).
  - intros τ Hτ.
    exact (in_enumT_ex_implies_T_ex τ Hτ).
  - exact periodic_window_dbf_test.
Qed.

Theorem periodic_example_llf_schedulable_by_classical_dbf_generated_with_busy_prefix_bridge :
  (forall t, taskset_periodic_dbf tasks_ex enumT_ex t <= t) ->
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
  intros Hdbf_classical Hjob_bridge.
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
  eapply periodic_llf_schedulable_by_classical_dbf_on_finite_horizon_auto_with_busy_prefix_bridge
    with (enumT := enumT_ex) (sched := sched); eauto.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_nodup.
  - intros τ Hτ.
    exact (T_ex_in_enumT_ex τ Hτ).
  - intros τ Hτ.
    exact (in_enumT_ex_implies_T_ex τ Hτ).
Qed.
