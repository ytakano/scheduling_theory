From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From SchedulingTheory Require Import Uniprocessor.Policies.EDF.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicTasks.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicEDFBridge.
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

Definition job0_ex : Job := mkJob 0 0 0 1 2.
Definition job1_ex : Job := mkJob 1 0 0 1 3.
Definition job2_ex : Job := mkJob 0 1 2 1 4.
Definition other_job_ex : Job := mkJob 2 0 10 1 15.

Definition jobs_ex (j : JobId) : Job :=
  match j with
  | 0 => job0_ex
  | 1 => job1_ex
  | 2 => job2_ex
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

Definition enumJ_ex : list JobId := [0; 1; 2].

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

Lemma enumJ_ex_sound :
  forall j, In j enumJ_ex -> periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j.
Proof.
  intros j Hj.
  unfold enumJ_ex in Hj.
  simpl in Hj.
  unfold periodic_jobset_upto, T_ex, H_ex, jobs_ex.
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j; simpl.
  - split.
    + left. reflexivity.
    + split.
      * exact generated_job0_ex.
      * lia.
  - split.
    + right. reflexivity.
    + split.
      * exact generated_job1_ex.
      * lia.
  - split.
    + left. reflexivity.
    + split.
      * exact generated_job2_ex.
      * lia.
Qed.

Lemma enumJ_ex_complete :
  forall j, periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex j -> In j enumJ_ex.
Proof.
  intros j Hj.
  destruct j as [| [| [| j']]]; simpl; try tauto.
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
  destruct t as [| [| [| t']]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed, jobs_ex, job0_ex, job1_ex, job2_ex;
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
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j;
    unfold completed, jobs_ex, job0_ex, job1_ex, job2_ex, sched_ex;
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
