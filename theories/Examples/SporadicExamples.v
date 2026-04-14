From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Common.WitnessCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.
From RocqSched Require Import TaskModels.Sporadic.SporadicFiniteHorizon.
From RocqSched Require Import TaskModels.Sporadic.SporadicWorkload.
From RocqSched Require Import TaskModels.Sporadic.SporadicEnumeration.
From RocqSched Require Import TaskModels.Sporadic.SporadicPeriodicBridge.
From RocqSched Require Import TaskModels.Sporadic.SporadicEDFBridge.
From RocqSched Require Import TaskModels.Sporadic.SporadicLLFBridge.
From RocqSched Require Import TaskModels.Sporadic.SporadicPartitionedFiniteOptimalityLift.
Import ListNotations.

(* ===== Sporadic Task and Job Definitions ===== *)

(* Two sporadic tasks:
   τ0: cost=1, period=3, relative_deadline=3
   τ1: cost=1, period=5, relative_deadline=5 *)
Definition task_sp0_ex : Task := mkTask 1 3 3.
Definition task_sp1_ex : Task := mkTask 1 5 5.

Definition tasks_sp_ex (τ : TaskId) : Task :=
  match τ with
  | 0 => task_sp0_ex
  | 1 => task_sp1_ex
  | _ => mkTask 1 1 1
  end.

(* Three sporadic jobs within horizon H=5:
   j0: τ0, k=0, release=0, cost=1, abs_deadline=3
   j1: τ1, k=0, release=1, cost=1, abs_deadline=6  (sporadic: arrives at t=1, not t=0)
   j2: τ0, k=1, release=4, cost=1, abs_deadline=7  (≥ 0 + 1*3 = 3 ✓) *)
Definition job_sp0_ex : Job := mkJob 0 0 0 1 3.
Definition job_sp1_ex : Job := mkJob 1 0 1 1 6.
Definition job_sp2_ex : Job := mkJob 0 1 4 1 7.
(* Out-of-scope job: task=2, not in T_sp_ex *)
Definition other_job_sp_ex : Job := mkJob 2 0 10 1 11.

Definition jobs_sp_ex (j : JobId) : Job :=
  match j with
  | 0 => job_sp0_ex
  | 1 => job_sp1_ex
  | 2 => job_sp2_ex
  | _ => other_job_sp_ex
  end.

Definition T_sp_ex (τ : TaskId) : Prop := τ = 0 \/ τ = 1.

Definition T_sp_ex_bool (τ : TaskId) : bool :=
  Nat.eqb τ 0 || Nat.eqb τ 1.

Lemma T_sp_ex_bool_spec :
  forall τ, T_sp_ex_bool τ = true <-> T_sp_ex τ.
Proof.
  intro τ.
  unfold T_sp_ex_bool, T_sp_ex.
  split.
  - intro Hτ.
    apply orb_prop in Hτ.
    destruct Hτ as [Hτ | Hτ].
    + left. apply Nat.eqb_eq. exact Hτ.
    + right. apply Nat.eqb_eq. exact Hτ.
  - intro Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; reflexivity.
Qed.

Definition H_sp_ex : Time := 5.
Definition enumJ_sp_ex : list JobId := [0; 1; 2].

Lemma tasks_sp_ex_well_formed :
  well_formed_periodic_tasks_on T_sp_ex tasks_sp_ex.
Proof.
  intros τ Hτ.
  destruct Hτ as [Hτ | Hτ]; subst τ; simpl; lia.
Qed.

(* ===== Jobset Membership Proofs ===== *)

Lemma enumJ_sp_ex_sound :
  forall j,
    In j enumJ_sp_ex ->
    sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex j.
Proof.
  intros j Hj.
  simpl in Hj.
  unfold sporadic_jobset_upto, T_sp_ex, H_sp_ex.
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j;
    unfold jobs_sp_ex, job_sp0_ex, job_sp1_ex, job_sp2_ex,
           tasks_sp_ex, task_sp0_ex, task_sp1_ex;
    simpl.
  - split. { left. reflexivity. }
    split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                     valid_job_of_task. simpl. lia. }
    lia.
  - split. { right. reflexivity. }
    split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                     valid_job_of_task. simpl. lia. }
    lia.
  - split. { left. reflexivity. }
    split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                     valid_job_of_task. simpl. lia. }
    lia.
Qed.

Lemma enumJ_sp_ex_complete :
  forall j,
    sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex j ->
    In j enumJ_sp_ex.
Proof.
  intros j Hj.
  destruct j as [| [| [| j']]]; simpl; try tauto.
  unfold sporadic_jobset_upto, T_sp_ex, jobs_sp_ex in Hj.
  simpl in Hj.
  destruct Hj as [HT _].
  destruct HT as [HT | HT]; discriminate.
Qed.

Definition sporadic_witness_sp_ex
  : FiniteHorizonWitness
      (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) :=
  mkFiniteHorizonWitness
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    enumJ_sp_ex
    enumJ_sp_ex_complete
    enumJ_sp_ex_sound.

(* ===== Witness Schedule ===== *)

(* Uniprocessor schedule: j0 at t=0, j1 at t=1, j2 at t=4.
   All jobs complete within their deadlines. *)
Definition sched_sp_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 1 => Some 1
    | 4 => Some 2
    | _ => None
    end
  else None.

Lemma sched_sp_ex_valid :
  valid_schedule jobs_sp_ex 1 sched_sp_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia.
  subst c.
  unfold sched_sp_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| [| t']]]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_sp_ex, job_sp0_ex, job_sp1_ex, job_sp2_ex;
    simpl; lia.
Qed.

Lemma sporadic_feasible_schedule_sp_ex :
  feasible_schedule_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    jobs_sp_ex 1 sched_sp_ex.
Proof.
  unfold feasible_schedule_on.
  intros j Hj.
  apply enumJ_sp_ex_complete in Hj.
  unfold missed_deadline, enumJ_sp_ex in *.
  simpl in Hj.
  destruct Hj as [Hj | [Hj | [Hj | []]]]; subst j;
    unfold completed, jobs_sp_ex, job_sp0_ex, job_sp1_ex, job_sp2_ex, sched_sp_ex;
    simpl; lia.
Qed.

(* ===== Generation Predicate Demonstrations ===== *)

Lemma generated_sporadic_job0_ex :
  generated_by_sporadic_task tasks_sp_ex jobs_sp_ex 0.
Proof.
  unfold generated_by_sporadic_task, earliest_sporadic_release, valid_job_of_task,
         tasks_sp_ex, task_sp0_ex, jobs_sp_ex, job_sp0_ex. simpl. lia.
Qed.

Lemma generated_sporadic_job1_ex :
  generated_by_sporadic_task tasks_sp_ex jobs_sp_ex 1.
Proof.
  unfold generated_by_sporadic_task, earliest_sporadic_release, valid_job_of_task,
         tasks_sp_ex, task_sp1_ex, jobs_sp_ex, job_sp1_ex. simpl. lia.
Qed.

Lemma generated_sporadic_job2_ex :
  generated_by_sporadic_task tasks_sp_ex jobs_sp_ex 2.
Proof.
  unfold generated_by_sporadic_task, earliest_sporadic_release, valid_job_of_task,
         tasks_sp_ex, task_sp0_ex, jobs_sp_ex, job_sp2_ex. simpl. lia.
Qed.

Lemma sporadic_jobset_unique_index_sp_ex :
  unique_task_index_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    jobs_sp_ex.
Proof.
  intros j1 j2 Hj1 Hj2 Htask Hidx.
  apply enumJ_sp_ex_complete in Hj1.
  apply enumJ_sp_ex_complete in Hj2.
  unfold enumJ_sp_ex in *.
  simpl in Hj1, Hj2.
  destruct Hj1 as [Hj1 | [Hj1 | [Hj1 | []]]];
  destruct Hj2 as [Hj2 | [Hj2 | [Hj2 | []]]];
    subst; simpl in *; try congruence.
Qed.

Lemma sporadic_jobset_separation_sp_ex :
  sporadic_separation_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    tasks_sp_ex jobs_sp_ex.
Proof.
  intros j1 j2 Hj1 Hj2 Htask Hlt.
  apply enumJ_sp_ex_complete in Hj1.
  apply enumJ_sp_ex_complete in Hj2.
  unfold enumJ_sp_ex in *.
  simpl in Hj1, Hj2.
  destruct Hj1 as [Hj1 | [Hj1 | [Hj1 | []]]];
  destruct Hj2 as [Hj2 | [Hj2 | [Hj2 | []]]];
    subst; simpl in *; try lia; try congruence.
Qed.

Lemma sporadic_example_task0_job_count_bound :
  length [0; 2] <= sporadic_jobs_of_task_upto_bound T_sp_ex tasks_sp_ex 0 H_sp_ex.
Proof.
  eapply sporadic_job_count_upto_le.
  - exact tasks_sp_ex_well_formed.
  - simpl. constructor.
    + intro H. simpl in H. lia.
    + constructor.
      * intro H. contradiction.
      * constructor.
  - exact sporadic_jobset_unique_index_sp_ex.
  - exact sporadic_jobset_separation_sp_ex.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | [Hj | []]]; subst j.
    + split.
      * exact (enumJ_sp_ex_sound 0 (or_introl eq_refl)).
      * reflexivity.
    + split.
      * exact (enumJ_sp_ex_sound 2 (or_intror (or_intror (or_introl eq_refl)))).
      * reflexivity.
Qed.

Lemma sporadic_example_task0_workload_bound :
  total_job_cost jobs_sp_ex [0; 2] <= sporadic_workload_upto_bound tasks_sp_ex 0 H_sp_ex.
Proof.
  eapply sporadic_workload_upto_le.
  - exact tasks_sp_ex_well_formed.
  - simpl. constructor.
    + intro H. simpl in H. lia.
    + constructor.
      * intro H. contradiction.
      * constructor.
  - exact sporadic_jobset_unique_index_sp_ex.
  - exact sporadic_jobset_separation_sp_ex.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | [Hj | []]]; subst j.
    + split.
      * exact (enumJ_sp_ex_sound 0 (or_introl eq_refl)).
      * reflexivity.
    + split.
      * exact (enumJ_sp_ex_sound 2 (or_intror (or_intror (or_introl eq_refl)))).
      * reflexivity.
Qed.

Lemma sporadic_feasible_on_sp_ex :
  feasible_on (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) jobs_sp_ex 1.
Proof.
  exists sched_sp_ex.
  split.
  - exact sched_sp_ex_valid.
  - exact sporadic_feasible_schedule_sp_ex.
Qed.

(* ===== Main Theorems ===== *)

(* The sporadic job set is EDF-schedulable on 1 CPU. *)
Theorem sporadic_example_edf_schedulable_by_on :
  schedulable_by_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    (edf_scheduler
       (witness_candidates_of
          (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
          sporadic_witness_sp_ex))
    jobs_sp_ex 1.
Proof.
  eapply sporadic_edf_optimality_on_finite_horizon.
  - exact T_sp_ex_bool_spec.
  - exact sporadic_feasible_on_sp_ex.
Qed.

(* The same sporadic job set is LLF-schedulable on 1 CPU. *)
Theorem sporadic_example_llf_schedulable_by_on :
  schedulable_by_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    (llf_scheduler
       (witness_candidates_of
          (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
          sporadic_witness_sp_ex))
    jobs_sp_ex 1.
Proof.
  eapply sporadic_llf_optimality_on_finite_horizon.
  - exact T_sp_ex_bool_spec.
  - exact sporadic_feasible_on_sp_ex.
Qed.

(* ===== Partitioned Sporadic EDF Example ===== *)

(* Static assignment: j1 (τ1, k=0) goes to CPU 1; j0 and j2 (τ0) go to CPU 0.
   CPU 0: {j0, j2}   CPU 1: {j1} *)
Definition assign_sp_ex (j : JobId) : CPU :=
  if Nat.eqb j 1 then 1 else 0.

Lemma assign_sp_ex_valid : forall j, assign_sp_ex j < 2.
Proof.
  intro j. unfold assign_sp_ex.
  destruct (Nat.eqb j 1); simpl; lia.
Qed.

(* CPU 0 local schedule: j0 at t=0, j2 at t=4. *)
Definition sched_sp_c0_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 4 => Some 2
    | _ => None
    end
  else None.

(* CPU 1 local schedule: j1 at t=1. *)
Definition sched_sp_c1_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 1 => Some 1
    | _ => None
    end
  else None.

Lemma sched_sp_c0_ex_valid : valid_schedule jobs_sp_ex 1 sched_sp_c0_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia. subst c.
  unfold sched_sp_c0_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| [| t']]]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_sp_ex, job_sp0_ex, job_sp2_ex;
    simpl; lia.
Qed.

Lemma sched_sp_c1_ex_valid : valid_schedule jobs_sp_ex 1 sched_sp_c1_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia. subst c.
  unfold sched_sp_c1_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| t']]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed,
           jobs_sp_ex, job_sp1_ex;
    simpl; lia.
Qed.

Lemma local_jobset_sp_c0_ex :
  forall j,
    local_jobset assign_sp_ex
      (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) 0 j <->
    j = 0 \/ j = 2.
Proof.
  intro j.
  unfold local_jobset, assign_sp_ex, sporadic_jobset_upto, T_sp_ex, H_sp_ex, jobs_sp_ex.
  split.
  - intros [[HT [Hgen Hrel]] Hassign].
    destruct j as [| [| [| j']]]; simpl in Hassign; try discriminate.
    + left. reflexivity.
    + right. reflexivity.
    + simpl in HT. destruct HT as [HT | HT]; discriminate.
  - intros [Hj | Hj]; subst j; simpl.
    + split.
      * split. { left. reflexivity. }
        split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                         valid_job_of_task, task_sp0_ex, job_sp0_ex. simpl. lia. }
        lia.
      * reflexivity.
    + split.
      * split. { left. reflexivity. }
        split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                         valid_job_of_task, task_sp0_ex, job_sp2_ex. simpl. lia. }
        lia.
      * reflexivity.
Qed.

Lemma local_jobset_sp_c1_ex :
  forall j,
    local_jobset assign_sp_ex
      (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) 1 j <->
    j = 1.
Proof.
  intro j.
  unfold local_jobset, assign_sp_ex, sporadic_jobset_upto, T_sp_ex, H_sp_ex, jobs_sp_ex.
  split.
  - intros [[HT [Hgen Hrel]] Hassign].
    destruct j as [| [| [| j']]]; simpl in Hassign; try discriminate.
    reflexivity.
  - intros Hj; subst j; simpl.
    split.
    + split. { right. reflexivity. }
      split. { unfold generated_by_sporadic_task, earliest_sporadic_release,
                       valid_job_of_task, task_sp1_ex, job_sp1_ex. simpl. lia. }
      lia.
    + reflexivity.
Qed.

Lemma local_feasible_sp_cpu0_ex :
  feasible_on
    (local_jobset assign_sp_ex
       (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) 0)
    jobs_sp_ex 1.
Proof.
  exists sched_sp_c0_ex.
  split.
  - exact sched_sp_c0_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    apply local_jobset_sp_c0_ex in Hj.
    destruct Hj as [Hj | Hj]; subst j;
      unfold missed_deadline, completed,
             jobs_sp_ex, job_sp0_ex, job_sp2_ex, sched_sp_c0_ex;
      simpl; lia.
Qed.

Lemma local_feasible_sp_cpu1_ex :
  feasible_on
    (local_jobset assign_sp_ex
       (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex) 1)
    jobs_sp_ex 1.
Proof.
  exists sched_sp_c1_ex.
  split.
  - exact sched_sp_c1_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    apply local_jobset_sp_c1_ex in Hj.
    subst j.
    unfold missed_deadline, completed,
           jobs_sp_ex, job_sp1_ex, sched_sp_c1_ex;
    simpl; lia.
Qed.

(* The sporadic job set is schedulable by a 2-CPU partitioned EDF scheduler. *)
Theorem sporadic_example_partitioned_edf_schedulable_by_on :
  schedulable_by_on
    (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
    (partitioned_scheduler 2 edf_generic_spec
       (enum_local_candidates_of assign_sp_ex
          (witness_enumJ
             (sporadic_jobset_upto T_sp_ex tasks_sp_ex jobs_sp_ex H_sp_ex)
             sporadic_witness_sp_ex)))
    jobs_sp_ex 2.
Proof.
  apply (partitioned_sporadic_finite_optimality_lift_with_witness
           edf_scheduler edf_generic_spec
           (fun _ => eq_refl)
           (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
              edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
           assign_sp_ex 2 assign_sp_ex_valid
           T_sp_ex T_sp_ex_bool tasks_sp_ex H_sp_ex jobs_sp_ex sporadic_witness_sp_ex).
  - exact T_sp_ex_bool_spec.
  - intros c Hc.
    destruct c as [| [| c]]; try lia.
    + exact local_feasible_sp_cpu0_ex.
    + exact local_feasible_sp_cpu1_ex.
Qed.
