From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

(* ================================================================ *)
(* 1. A concrete periodic task set                                  *)
(* ================================================================ *)

(* We choose long periods so that, inside the finite horizon H_ex = 4,
   each task releases only one job. This keeps the example small and
   makes the horizon-side condition immediate. *)

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

Definition H_ex : Time := 4.

Definition enumT_ex : list TaskId := [0; 1].

(* ================================================================ *)
(* 2. Concrete jobs                                                  *)
(* ================================================================ *)

(* Since H_ex = 4 and the periods are 5 and 7, only the first job of
   each in-scope task is released before H_ex. *)

Definition job0_ex : Job := mkJob 0 0 0 1 2.
Definition job1_ex : Job := mkJob 1 0 0 1 3.

(* A default out-of-scope job used for all other job IDs. *)
Definition other_job_ex : Job := mkJob 2 0 10 1 110.

Definition jobs_ex (j : JobId) : Job :=
  match j with
  | 0 => job0_ex
  | 1 => job1_ex
  | _ => other_job_ex
  end.

(* ================================================================ *)
(* 3. Basic generation facts                                         *)
(* ================================================================ *)

Lemma generated_job0_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex 0.
Proof.
  unfold generated_by_periodic_task, jobs_ex, job0_ex, tasks_ex, task0_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job1_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex 1.
Proof.
  unfold generated_by_periodic_task, jobs_ex, job1_ex, tasks_ex, task1_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

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
(* 4. A concrete finite-horizon codec                                *)
(* ================================================================ *)

(* There are only two in-scope jobs inside the horizon:
   (task 0, index 0) -> job 0
   (task 1, index 0) -> job 1
   everything else    -> job 2 (irrelevant default) *)

Definition job_id_of_ex (tau : TaskId) (k : nat) : JobId :=
  match tau, k with
  | 0, 0 => 0
  | 1, 0 => 1
  | _, _ => 2
  end.

Lemma codec_ex_sound :
  forall tau k,
    T_ex tau ->
    expected_release tasks_ex offset_ex tau k < H_ex ->
    let j := job_id_of_ex tau k in
    job_task (jobs_ex j) = tau /\
    job_index (jobs_ex j) = k /\
    generated_by_periodic_task tasks_ex offset_ex jobs_ex j.
Proof.
  intros tau k Htau Hrel.
  destruct Htau as [-> | ->].
  - assert (k = 0).
    { unfold expected_release, tasks_ex, task0_ex, offset_ex, H_ex in Hrel.
      simpl in Hrel. lia. }
    subst k.
    simpl.
    split; [reflexivity |].
    split; [reflexivity |].
    exact generated_job0_ex.
  - assert (k = 0).
    { unfold expected_release, tasks_ex, task1_ex, offset_ex, H_ex in Hrel.
      simpl in Hrel. lia. }
    subst k.
    simpl.
    split; [reflexivity |].
    split; [reflexivity |].
    exact generated_job1_ex.
Qed.

Lemma codec_ex_complete :
  forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    j = job_id_of_ex (job_task (jobs_ex j)) (job_index (jobs_ex j)).
Proof.
  intros j Hj.
  destruct j as [| [| j']]; simpl; try reflexivity.
  unfold periodic_jobset_upto, jobs_ex, other_job_ex, H_ex in Hj.
  simpl in Hj.
  destruct Hj as [_ [_ Hrel]].
  lia.
Qed.

Definition codec_ex : PeriodicFiniteHorizonCodec T_ex tasks_ex offset_ex jobs_ex H_ex :=
  mkPeriodicFiniteHorizonCodec
    T_ex tasks_ex offset_ex jobs_ex H_ex
    job_id_of_ex
    codec_ex_sound
    codec_ex_complete.

(* ================================================================ *)
(* 5. The generated job list and generated EDF schedule              *)
(* ================================================================ *)

Definition enumJ_ex : list JobId :=
  enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex.

Definition sched_gen_ex : Schedule :=
  generated_schedule
    edf_generic_spec
    (enum_candidates_of enumJ_ex)
    jobs_ex.

Example enumJ_ex_is_small :
  enumJ_ex = [0; 1].
Proof.
  reflexivity.
Qed.

(* ================================================================ *)
(* 6. User obligations                                               *)
(* ================================================================ *)

Definition periodic_window_dbf_bound_ex : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    t2 <= H_ex ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.

Definition generated_edf_busy_prefix_bridge_ex : Prop :=
  forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex H_ex
      sched_gen_ex
      j.

Lemma deadlines_within_horizon_ex :
  forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    job_abs_deadline (jobs_ex j) <= H_ex.
Proof.
  intros j Hj.
  destruct j as [| [| j0]].
  - unfold H_ex. cbn. lia.
  - unfold H_ex. cbn. lia.
  - exfalso.
    pose proof
      (periodic_jobset_upto_implies_task_in_scope
         T_ex tasks_ex offset_ex jobs_ex H_ex (S (S j0)) Hj) as Hscope.
    unfold T_ex, jobs_ex, other_job_ex in Hscope.
    cbn in Hscope.
    destruct Hscope as [Hscope | Hscope]; lia.
Qed.

Section TutorialProof.

  Hypothesis Hdbf : periodic_window_dbf_bound_ex.
  Hypothesis Hbridge : generated_edf_busy_prefix_bridge_ex.

  Lemma generated_edf_busy_prefix_bridge_and_deadline_ex :
    forall j,
      periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
      job_abs_deadline (jobs_ex j) <= H_ex /\
      periodic_edf_busy_prefix_bridge
        T_ex tasks_ex offset_ex jobs_ex H_ex
        sched_gen_ex
        j.
  Proof.
    intros j Hj.
    split.
    - apply deadlines_within_horizon_ex; exact Hj.
    - apply Hbridge; exact Hj.
  Qed.

  Theorem tutorial_periodic_edf_schedulable :
    schedulable_by_on
      (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto
               T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
      jobs_ex 1.
  Proof.
    eapply
      periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_with_busy_prefix_bridge
      with (enumT := enumT_ex).
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact enumT_ex_complete.
    - exact enumT_ex_sound.
    - exact generated_edf_busy_prefix_bridge_and_deadline_ex.
    - exact Hdbf.
  Qed.

End TutorialProof.
