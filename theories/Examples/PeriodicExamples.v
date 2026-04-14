From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import Uniprocessor.Policies.EDFOptimality.
From RocqSched Require Import Multicore.Partitioned.Partitioned.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicReleaseLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicWorkload.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFBridge.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicPartitionedFiniteOptimalityLift.
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

Lemma tasks_ex_well_formed :
  well_formed_periodic_tasks_on T_ex tasks_ex.
Proof.
  intros τ Hτ.
  destruct Hτ as [Hτ | Hτ]; subst τ; simpl; lia.
Qed.

Lemma periodic_example_task0_job_count_bound :
  length [0] <= periodic_jobs_of_task_upto_count T_ex tasks_ex offset_ex 0 H_ex.
Proof.
  eapply (periodic_jobs_of_task_upto_count_sound
            T_ex tasks_ex offset_ex jobs_ex H_ex 0 [0]).
  - exact tasks_ex_well_formed.
  - simpl. constructor.
    + intro H. contradiction.
    + constructor.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []]; subst j.
    + split.
      * unfold periodic_jobset_upto, T_ex, jobs_ex, job0_ex, H_ex.
        simpl.
        split.
        { left. reflexivity. }
        split.
        { exact generated_job0_ex. }
        lia.
      * unfold jobs_ex, job0_ex. simpl. reflexivity.
Qed.

Lemma periodic_example_task0_workload_bound :
  total_job_cost jobs_ex [0] <= periodic_workload_upto tasks_ex 0 H_ex.
Proof.
  eapply (periodic_workload_upto_bound
            T_ex tasks_ex offset_ex jobs_ex H_ex 0 [0]).
  - exact tasks_ex_well_formed.
  - simpl. constructor.
    + intro H. contradiction.
    + constructor.
  - intros j Hj.
    simpl in Hj.
    destruct Hj as [Hj | []]; subst j.
    + split.
      * unfold periodic_jobset_upto, T_ex, jobs_ex, job0_ex, H_ex.
        simpl.
        split.
        { left. reflexivity. }
        split.
        { exact generated_job0_ex. }
        lia.
      * unfold jobs_ex, job0_ex. simpl. reflexivity.
Qed.

Lemma periodic_example_same_task_same_release_implies_same_index :
  job_index (jobs_ex 0) = job_index (jobs_ex 0).
Proof.
  eapply generated_by_periodic_same_task_same_release_implies_same_index.
  - exact tasks_ex_well_formed.
  - left. reflexivity.
  - exact generated_job0_ex.
  - exact generated_job0_ex.
  - reflexivity.
  - reflexivity.
Qed.

Lemma periodic_example_release_lt_horizon_implies_index_lt :
  forall τ k,
    T_ex τ ->
    expected_release tasks_ex offset_ex τ k < H_ex ->
    k < H_ex.
Proof.
  intros τ k Hτ Hrel.
  exact
    (expected_release_lt_horizon_implies_index_lt
       T_ex tasks_ex offset_ex τ k H_ex
       tasks_ex_well_formed Hτ Hrel).
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

(* ===== LLF examples ===== *)

(* The same periodic task set is LLF-schedulable on 1 CPU. *)
Theorem periodic_example_llf_schedulable_by_on :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (llf_scheduler (enum_candidates_of enumJ_ex))
    jobs_ex 1.
Proof.
  eapply periodic_llf_optimality_on_finite_horizon.
  - exact T_ex_bool_spec.
  - exact enumJ_ex_complete.
  - exact enumJ_ex_sound.
  - exact periodic_feasible_on_ex.
Qed.

Theorem periodic_example_llf_schedulable_by_on_auto :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (llf_scheduler
       (enum_candidates_of
          (enum_periodic_jobs_upto T_ex tasks_ex offset_ex jobs_ex H_ex enumT_ex codec_ex)))
    jobs_ex 1.
Proof.
  apply periodic_llf_optimality_on_finite_horizon_auto with (enumT := enumT_ex).
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; lia.
  - intros τ Hτ.
    destruct Hτ as [Hτ | Hτ]; subst τ; simpl; tauto.
  - intros τ Hτ.
    simpl in Hτ.
    destruct Hτ as [Hτ | [Hτ | []]]; subst τ.
    + left. reflexivity.
    + right. reflexivity.
  - exact periodic_feasible_on_ex.
Qed.

(* ===== Partitioned periodic EDF example ===== *)

(* Static assignment: task1 jobs (j=1, j=3) go to CPU 1; others to CPU 0.
   CPU 0: {job0 (task0,k=0), job2 (task0,k=1)}
   CPU 1: {job1 (task1,k=0), job3 (task1,k=1)} *)
Definition assign_ex (j : JobId) : CPU :=
  if Nat.eqb j 1 || Nat.eqb j 3 then 1 else 0.

Lemma assign_ex_valid : forall j, assign_ex j < 2.
Proof.
  intro j. unfold assign_ex.
  destruct (Nat.eqb j 1 || Nat.eqb j 3); simpl; lia.
Qed.

(* CPU 0 local schedule: job0 at t=0, job2 at t=2. *)
Definition sched_c0_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 0
    | 2 => Some 2
    | _ => None
    end
  else None.

(* CPU 1 local schedule: job1 at t=0, job3 at t=3. *)
Definition sched_c1_ex (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => Some 1
    | 3 => Some 3
    | _ => None
    end
  else None.

Lemma sched_c0_ex_valid : valid_schedule jobs_ex 1 sched_c0_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia. subst c.
  unfold sched_c0_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| t']]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed, jobs_ex, job0_ex, job2_ex; simpl; lia.
Qed.

Lemma sched_c1_ex_valid : valid_schedule jobs_ex 1 sched_c1_ex.
Proof.
  unfold valid_schedule.
  intros j t c Hc Hrun.
  assert (c = 0) by lia. subst c.
  unfold sched_c1_ex in Hrun.
  rewrite Nat.eqb_refl in Hrun.
  destruct t as [| [| [| [| t']]]]; simpl in Hrun; inversion Hrun; subst j;
    unfold eligible, released, completed, jobs_ex, job1_ex, job3_ex; simpl; lia.
Qed.

(* local_jobset assign_ex (periodic_jobset_upto T_ex ...) 0 = {0, 2} *)
Lemma local_jobset_c0_ex :
  forall j, local_jobset assign_ex (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex) 0 j <->
            j = 0 \/ j = 2.
Proof.
  intro j.
  unfold local_jobset, assign_ex, periodic_jobset_upto, T_ex, H_ex, jobs_ex.
  split.
  - intros [[HT [Hgen _]] Hassign].
    (* After destruct, assign_ex j = 0 fails (discrim) for j=1,3;
       remaining: j=0, j=2, j>=4. *)
    destruct j as [| [| [| [| j']]]]; simpl in Hassign; try discriminate.
    + left. reflexivity.     (* j = 0 *)
    + right. reflexivity.    (* j = 2 *)
    + simpl in HT. destruct HT as [HT | HT]; discriminate.  (* j >= 4: T_ex 2 = ⊥ *)
  - intros [Hj | Hj]; subst j; simpl.
    + split.
      * split. { left. reflexivity. }
        split. { exact generated_job0_ex. } { lia. }
      * reflexivity.
    + split.
      * split. { left. reflexivity. }
        split. { exact generated_job2_ex. } { lia. }
      * reflexivity.
Qed.

(* local_jobset assign_ex (periodic_jobset_upto T_ex ...) 1 = {1, 3} *)
Lemma local_jobset_c1_ex :
  forall j, local_jobset assign_ex (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex) 1 j <->
            j = 1 \/ j = 3.
Proof.
  intro j.
  unfold local_jobset, assign_ex, periodic_jobset_upto, T_ex, H_ex, jobs_ex.
  split.
  - intros [[HT [Hgen _]] Hassign].
    (* assign_ex j = 1 only for j=1,3; all others get 0=1 discrim. *)
    destruct j as [| [| [| [| j']]]]; simpl in Hassign; try discriminate.
    + left. reflexivity.     (* j = 1 *)
    + right. reflexivity.    (* j = 3 *)
  - intros [Hj | Hj]; subst j; simpl.
    + split.
      * split. { right. reflexivity. }
        split. { exact generated_job1_ex. } { lia. }
      * reflexivity.
    + split.
      * split. { right. reflexivity. }
        split. { exact generated_job3_ex. } { lia. }
      * reflexivity.
Qed.

Lemma local_feasible_cpu0_ex :
  feasible_on
    (local_jobset assign_ex (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex) 0)
    jobs_ex 1.
Proof.
  exists sched_c0_ex.
  split.
  - exact sched_c0_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    apply local_jobset_c0_ex in Hj.
    destruct Hj as [Hj | Hj]; subst j;
      unfold missed_deadline, completed, jobs_ex, job0_ex, job2_ex, sched_c0_ex;
      simpl; lia.
Qed.

Lemma local_feasible_cpu1_ex :
  feasible_on
    (local_jobset assign_ex (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex) 1)
    jobs_ex 1.
Proof.
  exists sched_c1_ex.
  split.
  - exact sched_c1_ex_valid.
  - unfold feasible_schedule_on.
    intros j Hj.
    apply local_jobset_c1_ex in Hj.
    destruct Hj as [Hj | Hj]; subst j;
      unfold missed_deadline, completed, jobs_ex, job1_ex, job3_ex, sched_c1_ex;
      simpl; lia.
Qed.

(* The periodic job set is schedulable by a 2-CPU partitioned EDF scheduler. *)
Theorem periodic_example_partitioned_edf_schedulable_by_on :
  schedulable_by_on
    (periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H_ex)
    (partitioned_scheduler 2 edf_generic_spec
       (enum_local_candidates_of assign_ex enumJ_ex))
    jobs_ex 2.
Proof.
  apply (partitioned_periodic_finite_optimality_lift
           edf_scheduler edf_generic_spec
           (fun _ => eq_refl)
           (fun J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf =>
              edf_optimality_on_finite_jobs J J_bool enumJ' cands cand_spec jobs' Hb Hc Hs Hf)
           assign_ex 2 assign_ex_valid
           T_ex T_ex_bool tasks_ex offset_ex H_ex enumJ_ex jobs_ex).
  - exact T_ex_bool_spec.
  - exact enumJ_ex_complete.
  - exact enumJ_ex_sound.
  - intros c Hc.
    destruct c as [| [| c]]; try lia.
    + exact local_feasible_cpu0_ex.
    + exact local_feasible_cpu1_ex.
Qed.
