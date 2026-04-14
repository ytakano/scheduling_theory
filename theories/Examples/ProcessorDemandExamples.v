From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicDemandBound.
From RocqSched Require Import TaskModels.Jitter.ReleaseJitter.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicDemandBound.

Import ListNotations.

Definition pd_task0 : Task := mkTask 2 5 4.
Definition pd_task1 : Task := mkTask 1 3 3.

Definition pd_tasks (τ : TaskId) : Task :=
  match τ with
  | 0 => pd_task0
  | _ => pd_task1
  end.

Example taskset_periodic_dbf_single_ex :
  taskset_periodic_dbf pd_tasks [0] 9 = 4.
Proof. reflexivity. Qed.

Example taskset_periodic_dbf_two_tasks_ex :
  taskset_periodic_dbf pd_tasks [0; 1] 9 = 7.
Proof. reflexivity. Qed.

Example taskset_periodic_dbf_app_ex :
  taskset_periodic_dbf pd_tasks [0; 1] 9 =
  taskset_periodic_dbf pd_tasks [0] 9 +
  taskset_periodic_dbf pd_tasks [1] 9.
Proof.
  change [0; 1] with ([0] ++ [1]).
  apply taskset_periodic_dbf_app.
Qed.

Example taskset_periodic_dbf_monotone_ex :
  taskset_periodic_dbf pd_tasks [0; 1] 9 <=
  taskset_periodic_dbf pd_tasks [0; 1] 10.
Proof.
  apply taskset_periodic_dbf_monotone. lia.
Qed.

Definition pd_busy_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    if t <? 4 then Some t else None
  else None.

Example pd_busy_interval_ex :
  busy_interval pd_busy_sched 0 4.
Proof.
  split.
  - lia.
  - intros t Ht.
    assert (Htlt : t < 4) by lia.
    exists t.
    unfold pd_busy_sched.
    rewrite Nat.eqb_refl.
    apply Nat.ltb_lt in Htlt.
    rewrite Htlt.
    reflexivity.
Qed.

Example busy_interval_supply_eq_length_ex :
  cpu_service_between pd_busy_sched 0 4 = 4.
Proof.
  apply busy_interval_cpu_supply_eq_length.
  exact pd_busy_interval_ex.
Qed.

Example demand_exceeds_busy_length_ex :
  cpu_service_between pd_busy_sched 0 4 < 5.
Proof.
  eapply demand_exceeds_busy_interval_length_contradiction.
  - exact pd_busy_interval_ex.
  - lia.
Qed.

Example busy_window_pd_ex :
  busy_window_candidate pd_busy_sched 0 4.
Proof.
  apply busy_interval_with_boundaries_is_busy_window_candidate.
  - exact pd_busy_interval_ex.
  - left. reflexivity.
  - unfold cpu_busy_at, pd_busy_sched.
    rewrite Nat.eqb_refl.
    intro Hbusy.
    destruct Hbusy as [j Hj].
    discriminate.
Qed.

Example periodic_processor_demand_witness_ex :
  periodic_processor_demand_witness pd_tasks [0; 0; 1] pd_busy_sched 0 4.
Proof.
  apply taskset_periodic_dbf_exceeds_busy_window_supply.
  - exact busy_window_pd_ex.
  - cbn. lia.
Qed.

Definition pd_sp_job : Job := mkJob 0 0 1 2 5.
Definition pd_sp_jobs (j : JobId) : Job := if Nat.eqb j 0 then pd_sp_job else mkJob 0 j 0 0 0.

Lemma pd_sp_job_in_deadline_jobset :
  sporadic_jobset_deadline_upto (fun _ => True) pd_tasks pd_sp_jobs 9 0.
Proof.
  unfold sporadic_jobset_deadline_upto, generated_by_sporadic_task,
         earliest_sporadic_release, valid_job_of_task,
         pd_sp_jobs, pd_sp_job, pd_tasks, pd_task0.
  simpl. repeat split; lia.
Qed.

Example sporadic_taskset_dbf_bound_ex :
  total_job_cost pd_sp_jobs [0] <= taskset_sporadic_dbf_bound pd_tasks [0] 9.
Proof.
  eapply (sporadic_total_demand_le_taskset_dbf
            (fun _ => True) pd_tasks pd_sp_jobs 9 [0] [0]).
  - intros τ _. unfold pd_tasks, pd_task0, pd_task1. destruct τ; simpl; lia.
  - intros τ Hin. simpl in Hin. destruct Hin as [<- | []].
    cbn. lia.
  - constructor; [simpl; tauto|constructor].
  - constructor; [simpl; tauto|constructor].
  - intros j1 j2 Hj1 Hj2 Htask Hidx.
    destruct j1, j2; simpl in *; try lia; reflexivity.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []].
    subst j.
    split.
    + exact pd_sp_job_in_deadline_jobset.
    + simpl. tauto.
Qed.

Definition pd_jp_job : Job := mkJob 0 0 1 2 5.
Definition pd_jp_jobs (j : JobId) : Job := if Nat.eqb j 0 then pd_jp_job else mkJob 0 j 0 0 0.
Definition pd_offset (_ : TaskId) : Time := 0.
Definition pd_jitter (_ : TaskId) : Time := 1.

Lemma pd_jp_job_in_deadline_jobset :
  jittered_periodic_jobset_deadline_upto
    (fun _ => True) pd_tasks pd_offset pd_jitter pd_jp_jobs 9 0.
Proof.
  unfold jittered_periodic_jobset_deadline_upto,
         generated_by_jittered_periodic_task, within_jitter, valid_job_of_task,
         expected_release, pd_jp_jobs, pd_jp_job, pd_offset, pd_jitter,
         pd_tasks, pd_task0.
  simpl. repeat split; lia.
Qed.

Example jittered_taskset_dbf_bound_ex :
  total_job_cost pd_jp_jobs [0] <=
  taskset_jittered_periodic_dbf_bound pd_tasks [0] 9.
Proof.
  eapply (jittered_periodic_total_demand_le_taskset_dbf
            (fun _ => True) pd_tasks pd_offset pd_jitter pd_jp_jobs 9 [0] [0]).
  - intros τ _. unfold pd_tasks, pd_task0, pd_task1. destruct τ; simpl; lia.
  - intros τ Hin. simpl in Hin. destruct Hin as [<- | []].
    cbn. lia.
  - constructor; [simpl; tauto|constructor].
  - constructor; [simpl; tauto|constructor].
  - intros j1 j2 Hj1 Hj2 Htask Hidx.
    destruct j1, j2; simpl in *; try lia; reflexivity.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []].
    subst j.
    split.
    + exact pd_jp_job_in_deadline_jobset.
    + simpl. tauto.
Qed.
