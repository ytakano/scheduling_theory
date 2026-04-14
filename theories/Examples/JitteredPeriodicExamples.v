From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.ReleaseJitter.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicTasks.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEnumeration.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicEDFBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicLLFBridge.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicPartitionedFiniteOptimalityLift.
Import ListNotations.

Definition task_jp0_ex : Task := mkTask 1 3 3.
Definition task_jp1_ex : Task := mkTask 1 5 5.

Definition tasks_jp_ex (τ : TaskId) : Task :=
  match τ with
  | 0 => task_jp0_ex
  | 1 => task_jp1_ex
  | _ => mkTask 1 1 1
  end.

Definition offset_jp_ex (_ : TaskId) : Time := 0.

Definition jitter_jp_ex (τ : TaskId) : Time :=
  match τ with
  | 0 => 1
  | 1 => 2
  | _ => 0
  end.

Definition job_jp0_ex : Job := mkJob 0 0 0 1 3.
Definition job_jp1_ex : Job := mkJob 1 0 1 1 6.
Definition job_jp2_ex : Job := mkJob 0 1 3 1 6.
Definition other_job_jp_ex : Job := mkJob 2 0 10 1 11.

Definition jobs_jp_ex (j : JobId) : Job :=
  match j with
  | 0 => job_jp0_ex
  | 1 => job_jp1_ex
  | 2 => job_jp2_ex
  | _ => other_job_jp_ex
  end.

Definition T_jp_ex (τ : TaskId) : Prop := τ = 0 \/ τ = 1.

Definition T_jp_ex_bool (τ : TaskId) : bool :=
  Nat.eqb τ 0 || Nat.eqb τ 1.

Lemma T_jp_ex_bool_spec :
  forall τ, T_jp_ex_bool τ = true <-> T_jp_ex τ.
Proof.
  intro τ.
  unfold T_jp_ex_bool, T_jp_ex.
  split.
  - intro Hτ.
    apply orb_prop in Hτ.
    destruct Hτ as [Hτ | Hτ].
    + left. apply Nat.eqb_eq. exact Hτ.
    + right. apply Nat.eqb_eq. exact Hτ.
  - intro Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; reflexivity.
Qed.

Definition H_jp_ex : Time := 5.
Definition enumJ_jp_ex : list JobId := [0; 1; 2].

Lemma generated_jittered_job0_ex :
  generated_by_jittered_periodic_task
    tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex 0.
Proof.
  unfold generated_by_jittered_periodic_task, within_jitter, valid_job_of_task,
         expected_release, tasks_jp_ex, offset_jp_ex, jitter_jp_ex,
         jobs_jp_ex, job_jp0_ex, task_jp0_ex.
  simpl. lia.
Qed.

Lemma generated_jittered_job1_ex :
  generated_by_jittered_periodic_task
    tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex 1.
Proof.
  unfold generated_by_jittered_periodic_task, within_jitter, valid_job_of_task,
         expected_release, tasks_jp_ex, offset_jp_ex, jitter_jp_ex,
         jobs_jp_ex, job_jp1_ex, task_jp1_ex.
  simpl. lia.
Qed.

Lemma generated_jittered_job2_ex :
  generated_by_jittered_periodic_task
    tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex 2.
Proof.
  unfold generated_by_jittered_periodic_task, within_jitter, valid_job_of_task,
         expected_release, tasks_jp_ex, offset_jp_ex, jitter_jp_ex,
         jobs_jp_ex, job_jp2_ex, task_jp0_ex.
  simpl. lia.
Qed.

Lemma jittered_release_differs_from_nominal_ex :
  job_release (jobs_jp_ex 1) <>
  expected_release tasks_jp_ex offset_jp_ex
    (job_task (jobs_jp_ex 1)) (job_index (jobs_jp_ex 1)).
Proof.
  unfold jobs_jp_ex, job_jp1_ex, expected_release, tasks_jp_ex, offset_jp_ex.
  simpl. discriminate.
Qed.

Lemma enumJ_jp_ex_sound :
  forall j,
    In j enumJ_jp_ex ->
    jittered_periodic_jobset_upto
      T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex j.
Proof.
  intros j Hj.
  simpl in Hj.
  unfold jittered_periodic_jobset_upto, T_jp_ex, H_jp_ex.
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j; simpl.
  - split. { left. reflexivity. }
    split. { exact generated_jittered_job0_ex. }
    lia.
  - split. { right. reflexivity. }
    split. { exact generated_jittered_job1_ex. }
    lia.
  - split. { left. reflexivity. }
    split. { exact generated_jittered_job2_ex. }
    lia.
Qed.

Lemma enumJ_jp_ex_complete :
  forall j,
    jittered_periodic_jobset_upto
      T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex j ->
    In j enumJ_jp_ex.
Proof.
  intros j Hj.
  destruct j as [| [| [| j']]]; simpl; try tauto.
  unfold jittered_periodic_jobset_upto, T_jp_ex, jobs_jp_ex in Hj.
  simpl in Hj.
  destruct Hj as [HT _].
  destruct HT as [HT | HT]; discriminate.
Qed.

Definition jittered_witness_jp_ex
  : JitteredPeriodicFiniteHorizonWitness
      T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex :=
  mkJitteredPeriodicFiniteHorizonWitness
    T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex
    enumJ_jp_ex
    enumJ_jp_ex_complete
    enumJ_jp_ex_sound.

Definition sched_jp_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 1 => Some 1
    | 3 => Some 2
    | _ => None
    end
  else None.

Lemma sched_jp_ex_valid :
  valid_schedule jobs_jp_ex 1 sched_jp_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia.
  subst c.
  unfold sched_jp_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| [| t']]]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_jp_ex, job_jp0_ex, job_jp1_ex, job_jp2_ex;
    simpl; lia.
Qed.

Lemma jittered_feasible_schedule_jp_ex :
  feasible_schedule_on
    (jittered_periodic_jobset_upto
       T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex)
    jobs_jp_ex 1 sched_jp_ex.
Proof.
  unfold feasible_schedule_on.
  intros j Hj.
  apply enumJ_jp_ex_complete in Hj.
  unfold missed_deadline, enumJ_jp_ex in *.
  simpl in Hj.
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j;
    unfold completed, jobs_jp_ex, job_jp0_ex, job_jp1_ex, job_jp2_ex, sched_jp_ex;
    simpl; lia.
Qed.

Lemma jittered_feasible_on_jp_ex :
  feasible_on
    (jittered_periodic_jobset_upto
       T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex)
    jobs_jp_ex 1.
Proof.
  exists sched_jp_ex.
  split.
  - exact sched_jp_ex_valid.
  - exact jittered_feasible_schedule_jp_ex.
Qed.

Theorem jittered_periodic_example_edf_schedulable_by_on :
  schedulable_by_on
    (jittered_periodic_jobset_upto
       T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex)
    (edf_scheduler
       (enum_candidates_of
          (jittered_enumJ
             T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex
             jittered_witness_jp_ex)))
    jobs_jp_ex 1.
Proof.
  eapply jittered_periodic_edf_optimality_on_finite_horizon.
  - exact T_jp_ex_bool_spec.
  - exact jittered_feasible_on_jp_ex.
Qed.

Theorem jittered_periodic_example_llf_schedulable_by_on :
  schedulable_by_on
    (jittered_periodic_jobset_upto
       T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex)
    (llf_scheduler
       (enum_candidates_of
          (jittered_enumJ
             T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex
             jittered_witness_jp_ex)))
    jobs_jp_ex 1.
Proof.
  eapply jittered_periodic_llf_optimality_on_finite_horizon.
  - exact T_jp_ex_bool_spec.
  - exact jittered_feasible_on_jp_ex.
Qed.

Definition assign_jp_ex (j : JobId) : CPU :=
  if Nat.eqb j 1 then 1 else 0.

Lemma assign_jp_ex_valid : forall j, assign_jp_ex j < 2.
Proof.
  intro j.
  unfold assign_jp_ex.
  destruct (Nat.eqb j 1); simpl; lia.
Qed.

Definition sched_jp_c0_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 3 => Some 2
    | _ => None
    end
  else None.

Definition sched_jp_c1_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 1 => Some 1
    | _ => None
    end
  else None.

Lemma sched_jp_c0_ex_valid :
  valid_schedule jobs_jp_ex 1 sched_jp_c0_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia.
  subst c.
  unfold sched_jp_c0_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| [| t']]]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_jp_ex, job_jp0_ex, job_jp1_ex, job_jp2_ex;
    simpl; lia.
Qed.

Lemma sched_jp_c1_ex_valid :
  valid_schedule jobs_jp_ex 1 sched_jp_c1_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia.
  subst c.
  unfold sched_jp_c1_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| [| t']]]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_jp_ex, job_jp0_ex, job_jp1_ex, job_jp2_ex;
    simpl; lia.
Qed.

Lemma jittered_local_feasible_cpu0 :
  feasible_on
    (local_jobset assign_jp_ex
       (jittered_periodic_jobset_upto
          T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex) 0)
    jobs_jp_ex 1.
Proof.
  exists sched_jp_c0_ex.
  split.
  - exact sched_jp_c0_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    unfold local_jobset in Hj.
    destruct Hj as [Hglob Hcpu].
    apply enumJ_jp_ex_complete in Hglob.
    unfold assign_jp_ex in Hcpu.
    unfold missed_deadline, enumJ_jp_ex in *.
    simpl in Hglob.
    destruct Hglob as [Hj0 | [Hj1 | [Hj2 | []]]]; subst j;
      simpl in Hcpu;
      try discriminate;
      unfold completed, jobs_jp_ex, job_jp0_ex, job_jp2_ex, sched_jp_c0_ex;
      simpl; lia.
Qed.

Lemma jittered_local_feasible_cpu1 :
  feasible_on
    (local_jobset assign_jp_ex
       (jittered_periodic_jobset_upto
          T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex) 1)
    jobs_jp_ex 1.
Proof.
  exists sched_jp_c1_ex.
  split.
  - exact sched_jp_c1_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    unfold local_jobset in Hj.
    destruct Hj as [Hglob Hcpu].
    apply enumJ_jp_ex_complete in Hglob.
    unfold assign_jp_ex in Hcpu.
    unfold missed_deadline, enumJ_jp_ex in *.
    simpl in Hglob.
    destruct Hglob as [Hj0 | [Hj1 | [Hj2 | []]]]; subst j;
      simpl in Hcpu;
      try discriminate;
      unfold completed, jobs_jp_ex, job_jp1_ex, sched_jp_c1_ex;
      simpl; lia.
Qed.

Theorem jittered_periodic_example_partitioned_edf_schedulable_by_on :
  schedulable_by_on
    (jittered_periodic_jobset_upto
       T_jp_ex tasks_jp_ex offset_jp_ex jitter_jp_ex jobs_jp_ex H_jp_ex)
    (partitioned_scheduler 2 edf_generic_spec
       (enum_local_candidates_of assign_jp_ex enumJ_jp_ex))
    jobs_jp_ex 2.
Proof.
  eapply partitioned_jittered_periodic_finite_optimality_lift
    with (local_scheduler := edf_scheduler).
  - intros cands. reflexivity.
  - intros J J_bool enumJ cands cand_spec jobs Hb Hc Hs Hf.
    exact (edf_optimality_on_finite_jobs J J_bool enumJ cands cand_spec jobs Hb Hc Hs Hf).
  - exact assign_jp_ex_valid.
  - exact T_jp_ex_bool_spec.
  - exact enumJ_jp_ex_complete.
  - exact enumJ_jp_ex_sound.
  - intros c Hc.
    destruct c.
    + exact jittered_local_feasible_cpu0.
    + destruct c.
      * exact jittered_local_feasible_cpu1.
      * lia.
Qed.
