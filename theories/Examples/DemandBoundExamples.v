From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicDemandBound.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicDemandBound.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.RequestBound.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.

Import ListNotations.

(**
  Examples/DemandBoundExamples.v
  ================================
  Concrete examples illustrating the Demand-Bound Function (DBF) API.

  We verify:
  1. Concrete periodic_dbf values for a simple task.
  2. periodic_dbf = 0 before the relative deadline.
  3. periodic_dbf at exactly the relative deadline.
  4. Monotonicity of periodic_dbf.
  5. sporadic_dbf_bound = periodic_dbf (definitionally).
  6. jittered_periodic_dbf_bound = periodic_dbf (definitionally).
  7. periodic_dbf ≤ periodic_rbf.
  8. Demand-bound bridge: total demand ≤ periodic_dbf for a concrete job list.
  9. Sporadic demand ≤ sporadic_dbf_bound.
*)

(* ===== Task definition ===== *)

(* Task: period = 5, wcet = 2, relative deadline = 4 (constrained deadline) *)
Definition dbf_example_task : Task := {|
  task_cost     := 2;
  task_period   := 5;
  task_relative_deadline := 4
|}.

Definition dbf_example_tasks : TaskId -> Task := fun _ => dbf_example_task.

(* ===== Example 1: periodic_dbf = 0 before deadline ===== *)

(* H = 3 < 4 = relative_deadline → dbf = 0 *)
Example periodic_dbf_ex_zero :
  periodic_dbf dbf_example_tasks 0 3 = 0.
Proof.
  apply periodic_dbf_zero_before_deadline.
  unfold dbf_example_tasks, dbf_example_task. simpl. lia.
Qed.

(* ===== Example 2: periodic_dbf at exactly the deadline ===== *)

(* H = 4 = relative_deadline → dbf = wcet = 2 *)
Example periodic_dbf_ex_at_deadline :
  periodic_dbf dbf_example_tasks 0 4 = 2.
Proof.
  apply periodic_dbf_at_deadline.
  unfold dbf_example_tasks, dbf_example_task. simpl. lia.
Qed.

(* ===== Example 3: concrete periodic_dbf values ===== *)

(* H = 9 = 4 + 5: two jobs have deadline ≤ 9 (job 0 at 4, job 1 at 9)
   dbf = S((9 - 4) / 5) * 2 = S(1) * 2 = 2 * 2 = 4 *)
Example periodic_dbf_ex1 :
  periodic_dbf dbf_example_tasks 0 9 = 4.
Proof. reflexivity. Qed.

(* H = 14 = 4 + 10: three jobs have deadline ≤ 14 (at 4, 9, 14)
   dbf = S((14 - 4) / 5) * 2 = S(2) * 2 = 3 * 2 = 6 *)
Example periodic_dbf_ex2 :
  periodic_dbf dbf_example_tasks 0 14 = 6.
Proof. reflexivity. Qed.

(* ===== Example 4: monotonicity ===== *)

Example periodic_dbf_monotone_ex :
  periodic_dbf dbf_example_tasks 0 9 <= periodic_dbf dbf_example_tasks 0 14.
Proof.
  apply periodic_dbf_monotone. lia.
Qed.

(* ===== Example 5: sporadic_dbf_bound = periodic_dbf ===== *)

Example sporadic_dbf_eq_periodic_ex :
  sporadic_dbf_bound dbf_example_tasks 0 9 =
  periodic_dbf dbf_example_tasks 0 9.
Proof. apply sporadic_dbf_bound_eq_periodic_dbf. Qed.

(* ===== Example 6: jittered_periodic_dbf_bound = periodic_dbf ===== *)

Example jittered_dbf_eq_periodic_ex :
  jittered_periodic_dbf_bound dbf_example_tasks 0 9 =
  periodic_dbf dbf_example_tasks 0 9.
Proof.
  rewrite jittered_periodic_dbf_bound_eq_sporadic_dbf.
  apply sporadic_dbf_bound_eq_periodic_dbf.
Qed.

(* ===== Example 7: periodic_dbf ≤ periodic_rbf ===== *)

(* For our task: dbf(H) ≤ rbf(H) for all H *)
Example periodic_dbf_le_rbf_ex :
  forall H, periodic_dbf dbf_example_tasks 0 H <=
            periodic_rbf dbf_example_tasks 0 H.
Proof.
  intro H.
  apply periodic_dbf_le_periodic_rbf.
  - unfold dbf_example_tasks, dbf_example_task. simpl. lia.
  - unfold dbf_example_tasks, dbf_example_task. simpl. lia.
Qed.

(* Concrete instance: dbf(9) = 4 ≤ rbf(9) = 4 *)
Example periodic_dbf_le_rbf_concrete :
  periodic_dbf dbf_example_tasks 0 9 <=
  periodic_rbf dbf_example_tasks 0 9.
Proof.
  apply periodic_dbf_le_periodic_rbf.
  - unfold dbf_example_tasks, dbf_example_task. simpl. lia.
  - unfold dbf_example_tasks, dbf_example_task. simpl. lia.
Qed.

(* ===== Example 8: demand-bound bridge for periodic tasks ===== *)

(* Set up a concrete job: released at 0, deadline 4, cost 2 (= job 0 of task 0). *)
Definition dbf_ex_job : Job := {|
  job_task         := 0;
  job_index        := 0;
  job_release      := 0;
  job_cost         := 2;
  job_abs_deadline := 4
|}.

Definition dbf_ex_jobs : JobId -> Job := fun _ => dbf_ex_job.
Definition dbf_ex_tasks : TaskId -> Task := dbf_example_tasks.
Definition dbf_ex_offset : TaskId -> Time := fun _ => 0.

Lemma dbf_ex_job_generated :
  generated_by_periodic_task dbf_ex_tasks dbf_ex_offset dbf_ex_jobs 0.
Proof.
  unfold generated_by_periodic_task, dbf_ex_jobs, dbf_ex_job,
         dbf_ex_tasks, dbf_example_tasks, dbf_example_task, dbf_ex_offset.
  simpl.
  repeat split; lia.
Qed.

Lemma dbf_ex_job_in_deadline_jobset :
  periodic_jobset_deadline_upto (fun _ => True) dbf_ex_tasks dbf_ex_offset
    dbf_ex_jobs 9 0.
Proof.
  unfold periodic_jobset_deadline_upto, dbf_ex_jobs, dbf_ex_job,
         dbf_ex_tasks, dbf_example_tasks, dbf_example_task, dbf_ex_offset.
  simpl.
  repeat split.
  - apply dbf_ex_job_generated.
  - lia.
Qed.

(* The workload of job 0 is bounded by the periodic DBF at horizon 9. *)
Example periodic_demand_le_dbf_ex :
  total_job_cost dbf_ex_jobs [0] <= periodic_dbf dbf_ex_tasks 0 9.
Proof.
  apply (periodic_demand_le_dbf
           (fun _ => True) dbf_ex_tasks dbf_ex_offset dbf_ex_jobs 9 0 [0]).
  - (* well_formed *)
    intros τ _.
    unfold dbf_ex_tasks, dbf_example_tasks, dbf_example_task. simpl. lia.
  - (* 0 < rel_deadline *)
    unfold dbf_ex_tasks, dbf_example_tasks, dbf_example_task. simpl. lia.
  - (* NoDup on indices *)
    constructor.
    + simpl. tauto.
    + constructor.
  - (* All jobs in jobset *)
    intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []].
    subst j.
    split.
    + apply dbf_ex_job_in_deadline_jobset.
    + reflexivity.
Qed.

(* ===== Example 9: sporadic demand ≤ sporadic_dbf_bound ===== *)

(* A sporadic job: arrived at time 1 (≥ 0 = 0*period), deadline 5, cost 2. *)
Definition dbf_sp_job : Job := {|
  job_task         := 0;
  job_index        := 0;
  job_release      := 1;
  job_cost         := 2;
  job_abs_deadline := 5    (* = release (1) + rel_deadline (4) *)
|}.

(* A null job used to fill all other job IDs; its deadline is wrong so it
   does NOT satisfy generated_by_sporadic_task, keeping uniqueness trivial. *)
Definition dbf_sp_null_job : Job := {|
  job_task         := 0;
  job_index        := 1;
  job_release      := 0;
  job_cost         := 0;
  job_abs_deadline := 0    (* ≠ 0 + 4 = release + rel_deadline, so not generated *)
|}.

Definition dbf_sp_jobs (j : JobId) : Job :=
  if Nat.eqb j 0 then dbf_sp_job else dbf_sp_null_job.

Lemma dbf_sp_job_generated :
  generated_by_sporadic_task dbf_ex_tasks dbf_sp_jobs 0.
Proof.
  unfold generated_by_sporadic_task, dbf_sp_jobs, dbf_sp_job,
         dbf_ex_tasks, dbf_example_tasks, dbf_example_task,
         earliest_sporadic_release, valid_job_of_task.
  simpl. repeat split; lia.
Qed.

Lemma dbf_sp_job_in_deadline_jobset :
  sporadic_jobset_deadline_upto (fun _ => True) dbf_ex_tasks
    dbf_sp_jobs 9 0.
Proof.
  unfold sporadic_jobset_deadline_upto, dbf_sp_jobs, dbf_sp_job,
         dbf_ex_tasks, dbf_example_tasks, dbf_example_task.
  simpl.
  constructor.
  - trivial.
  - constructor.
    + apply dbf_sp_job_generated.
    + simpl. lia.
Qed.

(* Only j = 0 satisfies the deadline-bounded predicate, because for j ≠ 0
   the null job has abs_deadline = 0 ≠ 0 + 4 = release + rel_deadline,
   which violates valid_job_of_task. *)
Lemma dbf_sp_jobs_unique_index :
  unique_task_index_on
    (sporadic_jobset_deadline_upto (fun _ => True) dbf_ex_tasks dbf_sp_jobs 9)
    dbf_sp_jobs.
Proof.
  intros j1 j2 Hj1 Hj2 _ _.
  destruct Hj1 as [_ [Hgen1 _]].
  destruct Hj2 as [_ [Hgen2 _]].
  (* Show j1 = 0 *)
  assert (Hj1_0 : j1 = 0).
  { destruct (Nat.eqb_spec j1 0) as [-> | Hne]; [reflexivity |].
    exfalso.
    destruct Hgen1 as [_ [Hdl_eq _]].
    unfold dbf_sp_jobs in Hdl_eq.
    apply Nat.eqb_neq in Hne.
    rewrite Hne in Hdl_eq.
    unfold dbf_sp_null_job, dbf_ex_tasks, dbf_example_tasks, dbf_example_task in *.
    simpl in Hdl_eq. lia. }
  (* Show j2 = 0 *)
  assert (Hj2_0 : j2 = 0).
  { destruct (Nat.eqb_spec j2 0) as [-> | Hne]; [reflexivity |].
    exfalso.
    destruct Hgen2 as [_ [Hdl_eq _]].
    unfold dbf_sp_jobs in Hdl_eq.
    apply Nat.eqb_neq in Hne.
    rewrite Hne in Hdl_eq.
    unfold dbf_sp_null_job, dbf_ex_tasks, dbf_example_tasks, dbf_example_task in *.
    simpl in Hdl_eq. lia. }
  subst. reflexivity.
Qed.

Example sporadic_demand_le_dbf_ex :
  total_job_cost dbf_sp_jobs [0] <= sporadic_dbf_bound dbf_ex_tasks 0 9.
Proof.
  apply (sporadic_demand_le_dbf
           (fun _ => True) dbf_ex_tasks dbf_sp_jobs 9 0 [0]).
  - intros τ _.
    unfold dbf_ex_tasks, dbf_example_tasks, dbf_example_task. simpl. lia.
  - unfold dbf_ex_tasks, dbf_example_tasks, dbf_example_task. simpl. lia.
  - constructor; [simpl; tauto | constructor].
  - exact dbf_sp_jobs_unique_index.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []]. subst j.
    split.
    + apply dbf_sp_job_in_deadline_jobset.
    + reflexivity.
Qed.
