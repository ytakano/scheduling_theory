From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
Import ListNotations.

Definition task0_ex : Task := mkTask 1 2 2.
Definition task1_ex : Task := mkTask 1 3 3.
Definition task2_ex : Task := mkTask 1 5 5.

Definition tasks_ex (τ : TaskId) : Task :=
  match τ with
  | 0 => task0_ex
  | 1 => task1_ex
  | _ => task2_ex
  end.

Definition offset_ex (_ : TaskId) : Time := 0.

Definition H_ex : Time := 4.

(* Four jobs in the finite horizon [0, 4):
   job0: task0 k=0, release=0, deadline=2
   job1: task1 k=0, release=0, deadline=3
   job2: task0 k=1, release=2, deadline=4
   job3: task1 k=1, release=3, deadline=6  *)
Definition job0_ex : Job := mkJob 0 0 0 1 2.
Definition job1_ex : Job := mkJob 1 0 0 1 3.
Definition job2_ex : Job := mkJob 0 1 2 1 4.
Definition job3_ex : Job := mkJob 1 1 3 1 6.
Definition other_job_ex : Job := mkJob 2 0 10 1 15.

Definition jobs_ex (j : JobId) : Job :=
  match j with
  | 0 => job0_ex
  | 1 => job1_ex
  | 2 => job2_ex
  | 3 => job3_ex
  | _ => other_job_ex
  end.

Definition T_ex (τ : TaskId) : Prop := τ = 0 \/ τ = 1.

Definition T_ex_bool (τ : TaskId) : bool :=
  Nat.eqb τ 0 || Nat.eqb τ 1.

Lemma T_ex_bool_spec :
  forall τ,
    T_ex_bool τ = true <-> T_ex τ.
Proof.
  intro τ.
  unfold T_ex_bool, T_ex.
  split.
  - intro Hτ.
    apply orb_prop in Hτ.
    destruct Hτ as [Hτ | Hτ].
    + left. apply Nat.eqb_eq. exact Hτ.
    + right. apply Nat.eqb_eq. exact Hτ.
  - intro Hτ.
    destruct Hτ as [Hτ | Hτ].
    + subst τ. simpl. reflexivity.
    + subst τ. simpl. reflexivity.
Qed.

Definition enumJ_ex : list JobId := [0; 1; 2; 3].

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

Lemma generated_job2_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex 2.
Proof.
  unfold generated_by_periodic_task, jobs_ex, job2_ex, tasks_ex, task0_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job3_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex 3.
Proof.
  unfold generated_by_periodic_task, jobs_ex, job3_ex, tasks_ex, task1_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma enumJ_ex_sound :
  forall j, In j enumJ_ex -> periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j.
Proof.
  intros j Hj.
  unfold enumJ_ex in Hj.
  simpl in Hj.
  unfold periodic_jobset_upto, T_ex, H_ex, jobs_ex.
  destruct Hj as [Hj | [Hj | [Hj | [Hj | []]]]]; subst j; simpl.
  - split.
    + left. reflexivity.
    + split. * exact generated_job0_ex. * lia.
  - split.
    + right. reflexivity.
    + split. * exact generated_job1_ex. * lia.
  - split.
    + left. reflexivity.
    + split. * exact generated_job2_ex. * lia.
  - split.
    + right. reflexivity.
    + split. * exact generated_job3_ex. * lia.
Qed.

Lemma enumJ_ex_complete :
  forall j, periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j -> In j enumJ_ex.
Proof.
  intros j Hj.
  destruct j as [| [| [| [| j']]]]; simpl; try tauto.
  unfold periodic_jobset_upto, T_ex, H_ex, jobs_ex in Hj.
  simpl in Hj.
  destruct Hj as [HT [_ _]].
  destruct HT as [HT | HT]; discriminate.
Qed.

Definition sched_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 1 => Some 1
    | 2 => Some 2
    | 3 => Some 3
    | _ => None
    end
  else None.

Lemma sched_ex_valid :
  valid_schedule jobs_ex 1 sched_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia.
  subst c.
  unfold sched_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| t']]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed, jobs_ex, job0_ex, job1_ex, job2_ex, job3_ex;
    simpl; lia.
Qed.

Lemma periodic_feasible_schedule_ex :
  feasible_schedule_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    jobs_ex 1 sched_ex.
Proof.
  unfold feasible_schedule_on.
  intros j Hj.
  apply enumJ_ex_complete in Hj.
  unfold missed_deadline, enumJ_ex in *.
  simpl in Hj.
  destruct Hj as [Hj | [Hj | [Hj | [Hj | []]]]]; subst j;
    unfold completed, jobs_ex, job0_ex, job1_ex, job2_ex, job3_ex, sched_ex;
    simpl; lia.
Qed.

Lemma periodic_feasible_on_ex :
  feasible_on (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex) jobs_ex 1.
Proof.
  exists sched_ex.
  split.
  - exact sched_ex_valid.
  - exact periodic_feasible_schedule_ex.
Qed.

Theorem periodic_example_edf_schedulable_by_on :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (edf_scheduler (enum_candidates_of enumJ_ex))
    jobs_ex 1.
Proof.
  eapply periodic_edf_optimality_on_finite_horizon.
  - exact T_ex_bool_spec.
  - exact enumJ_ex_complete.
  - exact enumJ_ex_sound.
  - exact periodic_feasible_on_ex.
Qed.

(* ===== Codec-based auto example ===== *)

(* Canonical mapping (task τ, index k) → JobId for the example. *)
Definition job_id_of_ex (τ : TaskId) (k : nat) : JobId :=
  match τ, k with
  | 0, 0 => 0
  | 1, 0 => 1
  | 0, 1 => 2
  | 1, 1 => 3
  | _, _ => 4
  end.

(* Soundness: for every (τ, k) with T_ex τ and expected_release < H_ex,
   job_id_of_ex maps to a job with the right task, index, and generation. *)
Lemma codec_ex_sound :
  forall τ k,
    T_ex τ ->
    expected_release tasks_ex offset_ex τ k < H_ex ->
    let j := job_id_of_ex τ k in
    job_task (jobs_ex j) = τ /\
    job_index (jobs_ex j) = k /\
    generated_by_periodic_task tasks_ex offset_ex jobs_ex j.
Proof.
  intros τ k HT Hrel.
  destruct HT as [Hτ | Hτ]; subst τ.
  - (* τ = 0, period = 2: valid k are 0 and 1 *)
    assert (Hk : k < 2).
    { unfold expected_release, H_ex, tasks_ex, task0_ex, offset_ex in Hrel. simpl in Hrel. lia. }
    destruct k as [| [| k']].
    + simpl. split; [reflexivity | split; [reflexivity | exact generated_job0_ex]].
    + simpl. split; [reflexivity | split; [reflexivity | exact generated_job2_ex]].
    + lia.
  - (* τ = 1, period = 3: valid k are 0 and 1 *)
    assert (Hk : k < 2).
    { unfold expected_release, H_ex, tasks_ex, task1_ex, offset_ex in Hrel. simpl in Hrel. lia. }
    destruct k as [| [| k']].
    + simpl. split; [reflexivity | split; [reflexivity | exact generated_job1_ex]].
    + simpl. split; [reflexivity | split; [reflexivity | exact generated_job3_ex]].
    + lia.
Qed.

(* Completeness: every job j in the periodic jobset equals job_id_of_ex applied
   to its task and index. *)
Lemma codec_ex_complete :
  forall j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j ->
    j = job_id_of_ex (job_task (jobs_ex j)) (job_index (jobs_ex j)).
Proof.
  intros j Hj.
  destruct j as [| [| [| [| j']]]]; simpl; try reflexivity.
  unfold periodic_jobset_upto, T_ex, jobs_ex in Hj.
  simpl in Hj.
  destruct Hj as [HT [_ _]].
  destruct HT as [HT | HT]; discriminate.
Qed.

Definition codec_ex : PeriodicFiniteHorizonCodec T_ex tasks_ex offset_ex jobs_ex H_ex :=
  mkPeriodicFiniteHorizonCodec
    T_ex tasks_ex offset_ex jobs_ex H_ex
    job_id_of_ex
    codec_ex_sound
    codec_ex_complete.

Definition enumT_ex : list TaskId := [0; 1].

Theorem periodic_example_edf_schedulable_by_on_auto :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (edf_scheduler
       (enum_candidates_of
          (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
    jobs_ex 1.
Proof.
  apply periodic_edf_optimality_on_finite_horizon_auto with (enumT := enumT_ex).
  - (* well_formed_periodic_tasks_on *)
    intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; lia.
  - (* T_ex τ -> In τ enumT_ex *)
    intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - (* In τ enumT_ex -> T_ex τ *)
    intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_feasible_on_ex.
Qed.
