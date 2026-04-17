From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

(* ================================================================ *)
(* 1. A concrete periodic task set                                  *)
(* ================================================================ *)

Definition task0_ex : Task := mkTask 1 5 2.
Definition task1_ex : Task := mkTask 1 7 3.

Definition tasks_ex (tau : TaskId) : Task :=
  match tau with
  | 0 => task0_ex
  | 1 => task1_ex
  | _ => mkTask 1 100 100
  end.

Definition T_ex (tau : TaskId) : Prop := tau = 0 \/ tau = 1.

Definition offset_ex (_ : TaskId) : Time := 0.

Definition enumT_ex : list TaskId := [0; 1].

(* ================================================================ *)
(* 2. Concrete infinite jobs                                         *)
(* ================================================================ *)

Definition jobs_ex : JobId -> Job :=
  canonical_periodic_jobs_from_enumT tasks_ex offset_ex enumT_ex.

Lemma tasks_ex_well_formed :
  well_formed_periodic_tasks_on T_ex tasks_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; lia.
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

Lemma enumT_ex_complete :
  forall tau, T_ex tau -> In tau enumT_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; tauto.
Qed.

Lemma enumT_ex_sound :
  forall tau, In tau enumT_ex -> T_ex tau.
Proof.
  intros tau Htau.
  simpl in Htau.
  destruct Htau as [Htau | [Htau | []]]; subst tau.
  - left; reflexivity.
  - right; reflexivity.
Qed.

(* ================================================================ *)
(* 3. A concrete global codec                                        *)
(* ================================================================ *)

Definition codec_ex : PeriodicCodec T_ex tasks_ex offset_ex jobs_ex :=
  zero_offset_periodic_codec_of_tasks
    T_ex tasks_ex enumT_ex
    enumT_ex_nodup
    enumT_ex_complete
    enumT_ex_sound
    ltac:(vm_compute; lia).

(* ================================================================ *)
(* 4. Concrete obligations for the infinite-time wrappers           *)
(* ================================================================ *)
Example periodic_classical_dbf_test_by_cutoff_ex :
  dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_classical_dbf_from_cutoff_ex :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  apply dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply enumT_ex_sound.
    exact Hin.
  - exact periodic_classical_dbf_test_by_cutoff_ex.
Qed.

Definition generated_edf_busy_prefix_no_carry_in_bridge_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.

Definition generated_edf_backlog_free_before_release_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_backlog_free_before_release
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.

Lemma generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex :
  generated_edf_backlog_free_before_release_ex ->
  generated_edf_busy_prefix_no_carry_in_bridge_ex.
Proof.
  intros Hbacklog j Hj.
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid.
    + exact tasks_ex_well_formed.
    + exact enumT_ex_complete.
    + exact enumT_ex_sound.
  - apply Hbacklog.
    exact Hj.
Qed.

Definition sched_inf_ex : Schedule :=
  generated_periodic_edf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.

Section TutorialClassicalProof.
  Hypothesis Hbacklog : generated_edf_backlog_free_before_release_ex.

  Definition tutorial_infinite_classical_obligations :
    PeriodicEDFConcreteInfiniteClassicalObligations
      T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.
  Proof.
    pose proof
      (generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex Hbacklog)
      as Hbridge.
    refine
      {| periodic_edf_concrete_infinite_tasks_wf := tasks_ex_well_formed;
         periodic_edf_concrete_infinite_enumT_nodup := enumT_ex_nodup;
         periodic_edf_concrete_infinite_enumT_complete := enumT_ex_complete;
         periodic_edf_concrete_infinite_enumT_sound := enumT_ex_sound;
         periodic_edf_concrete_infinite_offset_zero := _;
         periodic_edf_concrete_infinite_no_carry_in_bridge := Hbridge;
         periodic_edf_concrete_infinite_dbf_test_by_cutoff :=
           periodic_classical_dbf_test_by_cutoff_ex |}.
    intros τ _.
    reflexivity.
  Qed.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1 sched_inf_ex 0.
  Proof.
    pose proof tutorial_infinite_classical_obligations as Hobl.
    destruct Hobl as [Hwf Hnodup Hcomplete Hsound Hoff Hbridge' Hdbf].
    pose proof
      (global_periodic_job_id_of_sound
         T_ex tasks_ex offset_ex jobs_ex codec_ex 0 0
         (or_introl eq_refl)) as [_ [_ Hgen0]].
    apply periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge.
    - exact Hwf.
    - exact Hnodup.
    - exact Hcomplete.
    - exact Hsound.
    - exact Hoff.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact Hgen0.
    - apply Hbridge'.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact Hgen0.
    - eapply dbf_check_by_cutoff.
      + exact Hnodup.
      + intros τ Hin.
        apply Hwf.
        apply Hsound.
        exact Hin.
      + exact Hdbf.
  Qed.

  Theorem tutorial_periodic_edf_schedulable :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    apply periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations.
    exact tutorial_infinite_classical_obligations.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    exact tutorial_periodic_edf_schedulable.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf_direct :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact enumT_ex_complete.
    1: exact enumT_ex_sound.
    1: intros τ Hin; reflexivity.
    1: exact (generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex Hbacklog).
    1: exact periodic_classical_dbf_from_cutoff_ex.
  Qed.
End TutorialClassicalProof.
