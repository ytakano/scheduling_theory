From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Definition always_busy_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    if t <? 3 then Some t else None
  else None.

Example always_busy_sched_forms_busy_interval :
  busy_interval always_busy_sched 0 3.
Proof.
  split.
  - lia.
  - intros t Ht.
    exists t.
    unfold always_busy_sched.
    rewrite Nat.eqb_refl.
    assert (Htlt : t < 3) by lia.
    apply Nat.ltb_lt in Htlt.
    rewrite Htlt.
    reflexivity.
Qed.

Example always_busy_sched_maximal_on_prefix :
  maximal_busy_interval_from always_busy_sched 0 3.
Proof.
  split.
  - exact always_busy_sched_forms_busy_interval.
  - split.
    + left.
      reflexivity.
    + unfold cpu_busy_at, always_busy_sched.
      simpl.
      intro Hbusy.
      destruct Hbusy as [j Hj].
      discriminate.
Qed.

Example always_busy_sched_supply_matches_length :
  cpu_service_between always_busy_sched 0 3 = 3.
Proof.
  rewrite cpu_service_between_busy_interval_eq_length.
  - reflexivity.
  - exact always_busy_sched_forms_busy_interval.
Qed.

Definition idle_gap_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 1 => None
    | 2 => Some 1
    | _ => None
    end
  else None.

Example idle_gap_sched_not_busy_interval :
  ~ busy_interval idle_gap_sched 0 3.
Proof.
  apply (idle_slot_not_busy_interval idle_gap_sched 0 3 1).
  - lia.
  - unfold cpu_busy_at, idle_gap_sched.
    rewrite Nat.eqb_refl.
    intro Hbusy.
    destruct Hbusy as [j Hj].
    discriminate.
Qed.

Definition periodic_task_ex : Task := mkTask 1 2 2.

Definition periodic_tasks_ex (_ : TaskId) : Task := periodic_task_ex.

Definition periodic_offset_ex (_ : TaskId) : Time := 0.

Definition periodic_job0 : Job := mkJob 0 0 0 1 2.
Definition periodic_job1 : Job := mkJob 0 1 2 1 4.
Definition periodic_other_job : Job := mkJob 0 10 20 1 22.

Definition periodic_jobs_ex (j : JobId) : Job :=
  match j with
  | 0 => periodic_job0
  | 1 => periodic_job1
  | _ => periodic_other_job
  end.

Lemma periodic_job0_generated :
  generated_by_periodic_task periodic_tasks_ex periodic_offset_ex periodic_jobs_ex 0.
Proof.
  unfold generated_by_periodic_task, periodic_tasks_ex, periodic_offset_ex,
         periodic_jobs_ex, periodic_job0, periodic_task_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma periodic_job1_generated :
  generated_by_periodic_task periodic_tasks_ex periodic_offset_ex periodic_jobs_ex 1.
Proof.
  unfold generated_by_periodic_task, periodic_tasks_ex, periodic_offset_ex,
         periodic_jobs_ex, periodic_job1, periodic_task_ex.
  simpl.
  repeat split; lia.
Qed.

Definition periodic_busy_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 1 => Some 0
    | 2 => Some 1
    | 3 => Some 1
    | _ => None
    end
  else None.

Example periodic_front_interval_is_busy :
  busy_interval periodic_busy_sched 0 4.
Proof.
  split.
  - lia.
  - intros t Ht.
    exists (if t <? 2 then 0 else 1).
    unfold periodic_busy_sched.
    rewrite Nat.eqb_refl.
    destruct t as [| [| [| [| t']]]]; simpl in *; try reflexivity; lia.
Qed.

Example periodic_front_interval_supply :
  cpu_service_between periodic_busy_sched 0 4 = 4.
Proof.
  rewrite cpu_service_between_busy_interval_eq_length.
  - reflexivity.
  - exact periodic_front_interval_is_busy.
Qed.

Example periodic_front_interval_job0_service_bound :
  service_between 1 periodic_busy_sched 0 0 4 <= 4.
Proof.
  eapply service_between_le_busy_interval_length.
  exact periodic_front_interval_is_busy.
Qed.
