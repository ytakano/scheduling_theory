From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleTransform.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionInvariants.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateTable.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateSource.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Refinement.OSSchedulerRelationTheorem.
From RocqSched Require Import Multicore.Global.GlobalFIFO.
From RocqSched Require Import Uniprocessor.Policies.FIFO.

Definition workload_scheduler_facing_row_state
    (entry : AwkernelSchedTraceEntry) : OpState :=
  mkOpState
    (fun c => if Nat.eqb c 0 then sched_trace_primary_current entry else None)
    (aste_runnable entry)
    (fun c => if Nat.eqb c 0 then sched_trace_primary_need_resched entry else false)
    (fun c => if Nat.eqb c 0 then sched_trace_primary_dispatch_target entry else None).

Definition workload_scheduler_facing_choice
    (entry : AwkernelSchedTraceEntry) : list JobId :=
  match sched_trace_primary_current entry with
  | Some j => [j]
  | None => []
  end.

Definition workload_scheduler_facing_choice_head
    (entry : AwkernelSchedTraceEntry) : option JobId :=
  nth_error (workload_scheduler_facing_choice entry) 0.

Definition option_job_to_list (oj : option JobId) : list JobId :=
  match oj with
  | Some j => [j]
  | None => []
  end.

Definition append_job_once_preserving
    (xs : list JobId) (j : JobId) : list JobId :=
  if job_list_contains j xs then xs else xs ++ [j].

Fixpoint append_jobs_once_preserving
    (acc xs : list JobId) : list JobId :=
  match xs with
  | [] => acc
  | j :: xs' =>
      append_jobs_once_preserving
        (append_job_once_preserving acc j) xs'
  end.

Definition append_option_job_once_preserving
    (acc : list JobId) (oj : option JobId) : list JobId :=
  match oj with
  | Some j => append_job_once_preserving acc j
  | None => acc
  end.

Definition sched_trace_fifo_candidates
    (entry : AwkernelSchedTraceEntry) : list JobId :=
  append_option_job_once_preserving
    (append_jobs_once_preserving
       (option_job_to_list (sched_trace_primary_current entry))
       (aste_runnable entry))
    (sched_trace_primary_dispatch_target entry).

Definition sched_trace_fifo_head
    (entry : AwkernelSchedTraceEntry) : option JobId :=
  match sched_trace_fifo_candidates entry with
  | j :: _ => Some j
  | [] => None
  end.

Definition workload_global_fifo_choose_row
    (entry : AwkernelSchedTraceEntry) : Prop :=
  match aste_event entry with
  | EvChoose cpu j =>
      aste_cpu entry = 1 /\
      cpu = 1 /\
      sched_trace_fifo_head entry = Some j
  | _ => True
  end.

Definition sched_trace_global_fifo_rowb
    (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvChoose cpu j =>
      Nat.eqb (aste_cpu entry) 1 &&
      Nat.eqb cpu 1 &&
      option_job_eqb (sched_trace_fifo_head entry) (Some j)
  | _ => true
  end.

Fixpoint sched_trace_global_fifo_checkb
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  match sched_trace with
  | [] => true
  | entry :: sched_trace' =>
      sched_trace_global_fifo_rowb entry &&
      sched_trace_global_fifo_checkb sched_trace'
  end.

Fixpoint first_non_fifo_sched_trace_index_from
    (n : nat) (sched_trace : list AwkernelSchedTraceEntry) : option nat :=
  match sched_trace with
  | [] => None
  | entry :: sched_trace' =>
      if sched_trace_global_fifo_rowb entry
      then first_non_fifo_sched_trace_index_from (S n) sched_trace'
      else Some n
  end.

Definition first_non_fifo_sched_trace_index
    (sched_trace : list AwkernelSchedTraceEntry) : option nat :=
  first_non_fifo_sched_trace_index_from 0 sched_trace.

Definition sched_trace_global_fifo_family
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  Forall workload_global_fifo_choose_row sched_trace.

Definition accepted_workload_global_fifo_sched_trace_family
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  accepted_workload_sched_trace_family task_trace sched_trace /\
  task_trace_all_global_fifo_policyb task_trace = true /\
  sched_trace_global_fifo_family sched_trace.

Definition awk_workload_accepts_global_fifo_sched_trace
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  awk_workload_accepts_sched_trace task_trace sched_trace &&
  task_trace_all_global_fifo_policyb task_trace &&
  sched_trace_global_fifo_checkb sched_trace.

Fixpoint job_list_eqb (xs ys : list JobId) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && job_list_eqb xs' ys'
  | _, _ => false
  end.

Definition task_trace_blocks_at
    (task_trace : list AwkernelTaskTraceEntry)
    (event_id task_id : nat) : bool :=
  match summarize_task_trace initial_task_trace_summary task_trace with
  | Some summary => task_trace_blocked_at summary event_id task_id
  | None => false
  end.

Definition workload_scheduler_relation_candidates
    (task_trace : list AwkernelTaskTraceEntry)
    (entry : AwkernelSchedTraceEntry) : list JobId :=
  match aste_event entry with
  | EvChoose cpu j =>
      if Nat.eqb cpu 1 &&
         negb (task_trace_blocks_at task_trace (aste_event_id entry) j)
      then sched_trace_fifo_candidates entry
      else []
  | _ => []
  end.

Definition workload_fifo_candidate_row_contract
    (task_trace : list AwkernelTaskTraceEntry)
    (entry : AwkernelSchedTraceEntry) (cand : list JobId) : Prop :=
  cand = workload_scheduler_relation_candidates task_trace entry.

Definition workload_fifo_candidate_table
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : list (list JobId) :=
  map (workload_scheduler_relation_candidates task_trace) sched_trace.

Definition workload_fifo_candidate_table_contract
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : Prop :=
  length sched_trace = length table /\
  Forall2 (workload_fifo_candidate_row_contract task_trace) sched_trace table.

Definition workload_scheduler_relation_choice
    (task_trace : list AwkernelTaskTraceEntry)
    (entry : AwkernelSchedTraceEntry) : list JobId :=
  match aste_event entry with
  | EvChoose cpu j =>
      if Nat.eqb cpu 1 &&
         negb (task_trace_blocks_at task_trace (aste_event_id entry) j)
      then [j]
      else []
  | _ => []
  end.

Definition workload_scheduler_relation_schedule
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : Schedule :=
  fun t c =>
    if c <? 1 then
      nth_error
        (workload_scheduler_relation_choice
           task_trace
           (nth t sched_trace empty_sched_trace_entry))
        c
    else None.

Fixpoint task_trace_has_completeb
    (task_id : JobId) (task_trace : list AwkernelTaskTraceEntry) : bool :=
  match task_trace with
  | [] => false
  | entry :: task_trace' =>
      match atte_kind entry, atte_subject entry with
      | LkComplete, subject =>
          Nat.eqb subject task_id || task_trace_has_completeb task_id task_trace'
      | _, _ => task_trace_has_completeb task_id task_trace'
      end
  end.

Fixpoint count_scheduler_relation_service
    (task_trace : list AwkernelTaskTraceEntry)
    (task_id : JobId) (sched_trace : list AwkernelSchedTraceEntry) : nat :=
  match sched_trace with
  | [] => 0
  | entry :: sched_trace' =>
      let rest := count_scheduler_relation_service task_trace task_id sched_trace' in
      match workload_scheduler_relation_choice task_trace entry with
      | [j] => if Nat.eqb j task_id then S rest else rest
      | _ => rest
      end
  end.

Fixpoint first_scheduler_visible_index_from
    (task_trace : list AwkernelTaskTraceEntry)
    (task_id n : nat)
    (sched_trace : list AwkernelSchedTraceEntry) : option nat :=
  match sched_trace with
  | [] => None
  | entry :: sched_trace' =>
      if job_list_contains task_id
           (workload_scheduler_relation_candidates task_trace entry)
      then Some n
      else first_scheduler_visible_index_from task_trace task_id (S n) sched_trace'
  end.

Definition first_scheduler_visible_index
    (task_trace : list AwkernelTaskTraceEntry)
    (task_id : JobId)
    (sched_trace : list AwkernelSchedTraceEntry) : option nat :=
  first_scheduler_visible_index_from task_trace task_id 0 sched_trace.

Definition reconstructed_scheduler_relation_release
    (task_trace : list AwkernelTaskTraceEntry)
    (task_id : JobId)
    (sched_trace : list AwkernelSchedTraceEntry) : nat :=
  match first_scheduler_visible_index task_trace task_id sched_trace with
  | Some t => t
  | None => 0
  end.

Definition reconstructed_scheduler_relation_cost
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (task_id : JobId) : nat :=
  let service := count_scheduler_relation_service task_trace task_id sched_trace in
  if task_trace_has_completeb task_id task_trace
  then match service with
       | 0 => 1
       | _ => service
       end
  else S service.

Definition reconstructed_scheduler_relation_abs_deadline
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (task_id : JobId) : nat :=
  reconstructed_scheduler_relation_release task_trace task_id sched_trace +
  reconstructed_scheduler_relation_cost task_trace sched_trace task_id +
  length sched_trace.

Definition workload_scheduler_relation_jobs
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : JobId -> Job :=
  fun task_id =>
    mkJob
      task_id
      0
      (reconstructed_scheduler_relation_release task_trace task_id sched_trace)
      (reconstructed_scheduler_relation_cost task_trace sched_trace task_id)
      (reconstructed_scheduler_relation_abs_deadline task_trace sched_trace task_id)
      (fun _ => false).

Definition workload_global_fifo_scheduler_relation_row
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (t : Time)
    (entry : AwkernelSchedTraceEntry) : Prop :=
  choose_top_m
    global_fifo_top_m_spec
    (workload_scheduler_relation_jobs task_trace sched_trace)
    1
    (workload_scheduler_relation_schedule task_trace sched_trace)
    t
    (workload_scheduler_relation_candidates task_trace entry) =
  workload_scheduler_relation_choice task_trace entry.

Definition workload_global_fifo_scheduler_relation_rowb
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (t : Time)
    (entry : AwkernelSchedTraceEntry) : bool :=
  job_list_eqb
    (choose_top_m
       global_fifo_top_m_spec
       (workload_scheduler_relation_jobs task_trace sched_trace)
       1
       (workload_scheduler_relation_schedule task_trace sched_trace)
       t
       (workload_scheduler_relation_candidates task_trace entry))
    (workload_scheduler_relation_choice task_trace entry).

Fixpoint sched_trace_global_fifo_scheduler_relation_check_from
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (t : nat)
    (remaining : list AwkernelSchedTraceEntry) : bool :=
  match remaining with
  | [] => true
  | entry :: remaining' =>
      workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry &&
      sched_trace_global_fifo_scheduler_relation_check_from
        task_trace
        sched_trace
        (S t)
        remaining'
  end.

Definition sched_trace_global_fifo_scheduler_relation_checkb
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  sched_trace_global_fifo_scheduler_relation_check_from
    task_trace
    sched_trace
    0
    sched_trace.

Fixpoint first_non_scheduler_relation_sched_trace_index_from
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (t : nat)
    (remaining : list AwkernelSchedTraceEntry) : option nat :=
  match remaining with
  | [] => None
  | entry :: remaining' =>
      if workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry
      then first_non_scheduler_relation_sched_trace_index_from
             task_trace
             sched_trace
             (S t)
             remaining'
      else Some t
  end.

Definition first_non_scheduler_relation_sched_trace_index
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : option nat :=
  first_non_scheduler_relation_sched_trace_index_from
    task_trace
    sched_trace
    0
    sched_trace.

Fixpoint sched_trace_global_fifo_scheduler_relation_family_from
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (t : nat)
    (remaining : list AwkernelSchedTraceEntry) : Prop :=
  match remaining with
  | [] => True
  | entry :: remaining' =>
      workload_global_fifo_scheduler_relation_row task_trace sched_trace t entry /\
      sched_trace_global_fifo_scheduler_relation_family_from
        task_trace
        sched_trace
        (S t)
        remaining'
  end.

Definition sched_trace_global_fifo_scheduler_relation_family
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  sched_trace_global_fifo_scheduler_relation_family_from
    task_trace
    sched_trace
    0
    sched_trace.

Definition accepted_workload_global_fifo_scheduler_relation_family
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  accepted_workload_sched_trace_family task_trace sched_trace /\
  task_trace_all_global_fifo_policyb task_trace = true /\
  sched_trace_global_fifo_scheduler_relation_family task_trace sched_trace.

Definition awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  awk_workload_accepts_sched_trace task_trace sched_trace &&
  task_trace_all_global_fifo_policyb task_trace &&
  sched_trace_global_fifo_scheduler_relation_checkb task_trace sched_trace.

Definition workload_scheduler_facing_execution_matches_sched_trace
    {P : OSLabeledProjection AwkernelState}
    (ex : labeled_concrete_execution P 2)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  forall t,
    os_to_op_state (osl_to_os_projection P) (lce_trace ex t) =
    workload_scheduler_facing_row_state
      (nth t sched_trace empty_sched_trace_entry).

Definition workload_global_fifo_row_witness
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (entry : AwkernelSchedTraceEntry)
    (cand : list JobId) : Prop :=
  choose fifo_generic_spec jobs 1 sched t cand =
  workload_scheduler_facing_choice_head entry.

Definition workload_global_fifo_table_witness
    (jobs : JobId -> Job)
    (sched : Schedule)
    (sched_trace : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : Prop :=
  length sched_trace = length table /\
  forall t entry cand,
    nth_error sched_trace t = Some entry ->
    nth_error table t = Some cand ->
    workload_global_fifo_row_witness jobs sched t entry cand.

Definition accepted_workload_scheduler_facing_family
    (task_trace : list AwkernelTaskTraceEntry)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (sched_trace : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : Prop :=
  accepted_workload_sched_trace_family task_trace sched_trace /\
  workload_candidate_table_contract sched_trace table /\
  workload_global_fifo_table_witness jobs sched sched_trace table.

Lemma option_job_eqb_eq :
  forall x y,
    option_job_eqb x y = true <-> x = y.
Proof.
  intros [x|] [y|]; simpl.
  - rewrite Nat.eqb_eq. split; congruence.
  - split; discriminate.
  - split; discriminate.
  - split; intro H; [reflexivity|reflexivity].
Qed.

Lemma sched_trace_global_fifo_rowb_sound :
  forall entry,
    sched_trace_global_fifo_rowb entry = true ->
    workload_global_fifo_choose_row entry.
Proof.
  intros entry.
  unfold sched_trace_global_fifo_rowb, workload_global_fifo_choose_row.
  destruct (aste_event entry) as
      [j|j|j|j|c|c|c j|c j|c old new| |] eqn:Hevent; simpl; auto.
  intros H.
  apply Bool.andb_true_iff in H as [Hcpu Hhead].
  apply Bool.andb_true_iff in Hcpu as [Hcpu Heqcpu].
  apply Nat.eqb_eq in Hcpu.
  apply Nat.eqb_eq in Heqcpu.
  apply option_job_eqb_eq in Hhead.
  repeat split; assumption.
Qed.

Lemma sched_trace_global_fifo_rowb_complete :
  forall entry,
    workload_global_fifo_choose_row entry ->
    sched_trace_global_fifo_rowb entry = true.
Proof.
  intros entry.
  unfold sched_trace_global_fifo_rowb, workload_global_fifo_choose_row.
  destruct (aste_event entry) as
      [j|j|j|j|c|c|c j|c j|c old new| |] eqn:Hevent; simpl; auto.
  intros [Hcpu [Heqcpu Hhead]].
  apply Nat.eqb_eq in Hcpu.
  apply Nat.eqb_eq in Heqcpu.
  apply option_job_eqb_eq in Hhead.
  rewrite Hcpu, Heqcpu, Hhead.
  reflexivity.
Qed.

Lemma sched_trace_global_fifo_checkb_sound :
  forall sched_trace,
    sched_trace_global_fifo_checkb sched_trace = true ->
    sched_trace_global_fifo_family sched_trace.
Proof.
  intros sched_trace.
  induction sched_trace as [|entry sched_trace IH]; simpl; intros Hcheck.
  - constructor.
  - apply Bool.andb_true_iff in Hcheck as [Hrow Hrest].
    constructor.
    + apply sched_trace_global_fifo_rowb_sound. exact Hrow.
    + apply IH. exact Hrest.
Qed.

Lemma sched_trace_global_fifo_checkb_complete :
  forall sched_trace,
    sched_trace_global_fifo_family sched_trace ->
    sched_trace_global_fifo_checkb sched_trace = true.
Proof.
  intros sched_trace Hfamily.
  induction Hfamily; simpl.
  - reflexivity.
  - rewrite sched_trace_global_fifo_rowb_complete by exact H.
    rewrite IHHfamily.
    reflexivity.
Qed.

Lemma first_non_fifo_sched_trace_index_from_none :
  forall n sched_trace,
    first_non_fifo_sched_trace_index_from n sched_trace = None ->
    sched_trace_global_fifo_checkb sched_trace = true.
Proof.
  intros n sched_trace.
  revert n.
  induction sched_trace as [|entry sched_trace IH]; simpl; intros n Hnone.
  - reflexivity.
  - destruct (sched_trace_global_fifo_rowb entry) eqn:Hrow; try discriminate.
    apply IH in Hnone.
    exact Hnone.
Qed.

Lemma first_non_fifo_sched_trace_index_from_complete :
  forall n sched_trace,
    sched_trace_global_fifo_checkb sched_trace = true ->
    first_non_fifo_sched_trace_index_from n sched_trace = None.
Proof.
  intros n sched_trace.
  revert n.
  induction sched_trace as [|entry sched_trace IH]; simpl in *; intros n Hcheck.
  - reflexivity.
  - apply Bool.andb_true_iff in Hcheck as [Hrow Hrest].
    rewrite Hrow.
    apply IH.
    exact Hrest.
Qed.

Lemma first_non_fifo_sched_trace_index_none_complete :
  forall sched_trace,
    sched_trace_global_fifo_checkb sched_trace = true ->
    first_non_fifo_sched_trace_index sched_trace = None.
Proof.
  intros sched_trace Hcheck.
  unfold first_non_fifo_sched_trace_index.
  apply first_non_fifo_sched_trace_index_from_complete.
  exact Hcheck.
Qed.

Lemma awk_workload_accepts_global_fifo_sched_trace_sound :
  forall task_trace sched_trace,
    awk_workload_accepts_global_fifo_sched_trace task_trace sched_trace = true ->
    accepted_workload_global_fifo_sched_trace_family task_trace sched_trace.
Proof.
  intros task_trace sched_trace Haccept.
  unfold awk_workload_accepts_global_fifo_sched_trace in Haccept.
  apply Bool.andb_true_iff in Haccept as [Hfamily_policy Hfifo].
  apply Bool.andb_true_iff in Hfamily_policy as [Hfamily Hpolicy].
  split.
  - apply awk_workload_accepts_sched_trace_sound. exact Hfamily.
  - split.
    + exact Hpolicy.
    + apply sched_trace_global_fifo_checkb_sound. exact Hfifo.
Qed.

Lemma awk_workload_accepts_global_fifo_sched_trace_complete :
  forall task_trace sched_trace,
    accepted_workload_global_fifo_sched_trace_family task_trace sched_trace ->
    awk_workload_accepts_global_fifo_sched_trace task_trace sched_trace = true.
Proof.
  intros task_trace sched_trace [Hfamily [Hpolicy Hfifo]].
  unfold awk_workload_accepts_global_fifo_sched_trace.
  rewrite (awk_workload_accepts_sched_trace_complete task_trace sched_trace Hfamily).
  rewrite Hpolicy.
  rewrite (sched_trace_global_fifo_checkb_complete sched_trace Hfifo).
  reflexivity.
Qed.

Lemma job_list_eqb_eq :
  forall xs ys,
    job_list_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; simpl.
  - split; intro H; reflexivity.
  - split; discriminate.
  - split; discriminate.
  - split.
    + intro H.
      apply Bool.andb_true_iff in H as [Hxy Hrest].
      apply Nat.eqb_eq in Hxy.
      apply IH in Hrest.
      subst.
      reflexivity.
    + intro H.
      inversion H; subst.
      apply Bool.andb_true_iff.
      split.
      * apply Nat.eqb_eq. reflexivity.
      * apply IH. reflexivity.
Qed.

Lemma workload_global_fifo_scheduler_relation_rowb_sound :
  forall task_trace sched_trace t entry,
    workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry = true ->
    workload_global_fifo_scheduler_relation_row task_trace sched_trace t entry.
Proof.
  intros task_trace sched_trace t entry Hrow.
  unfold workload_global_fifo_scheduler_relation_rowb in Hrow.
  apply job_list_eqb_eq in Hrow.
  exact Hrow.
Qed.

Lemma workload_global_fifo_scheduler_relation_rowb_complete :
  forall task_trace sched_trace t entry,
    workload_global_fifo_scheduler_relation_row task_trace sched_trace t entry ->
    workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry = true.
Proof.
  intros task_trace sched_trace t entry Hrow.
  unfold workload_global_fifo_scheduler_relation_rowb.
  apply job_list_eqb_eq.
  exact Hrow.
Qed.

Lemma sched_trace_global_fifo_scheduler_relation_check_from_sound :
  forall task_trace sched_trace t remaining,
    sched_trace_global_fifo_scheduler_relation_check_from
      task_trace sched_trace t remaining = true ->
    sched_trace_global_fifo_scheduler_relation_family_from
      task_trace sched_trace t remaining.
Proof.
  intros task_trace sched_trace t remaining.
  revert t.
  induction remaining as [|entry remaining IH]; simpl; intros t Hcheck.
  - exact I.
  - apply Bool.andb_true_iff in Hcheck as [Hrow Hrest].
    split.
    + apply workload_global_fifo_scheduler_relation_rowb_sound.
      exact Hrow.
    + apply IH.
      exact Hrest.
Qed.

Lemma sched_trace_global_fifo_scheduler_relation_check_from_complete :
  forall task_trace sched_trace t remaining,
    sched_trace_global_fifo_scheduler_relation_family_from
      task_trace sched_trace t remaining ->
    sched_trace_global_fifo_scheduler_relation_check_from
      task_trace sched_trace t remaining = true.
Proof.
  intros task_trace sched_trace t remaining.
  revert t.
  induction remaining as [|entry remaining IH]; simpl; intros t Hfamily.
  - reflexivity.
  - destruct Hfamily as [Hrow Hrest].
    rewrite workload_global_fifo_scheduler_relation_rowb_complete by exact Hrow.
    rewrite IH by exact Hrest.
    reflexivity.
Qed.

Lemma first_non_scheduler_relation_sched_trace_index_from_none_sound :
  forall task_trace sched_trace t remaining,
    first_non_scheduler_relation_sched_trace_index_from
      task_trace sched_trace t remaining = None ->
    sched_trace_global_fifo_scheduler_relation_check_from
      task_trace sched_trace t remaining = true.
Proof.
  intros task_trace sched_trace t remaining.
  revert t.
  induction remaining as [|entry remaining IH]; simpl; intros t Hnone.
  - reflexivity.
  - destruct (workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry)
      eqn:Hrow; try discriminate.
    simpl.
    apply IH.
    exact Hnone.
Qed.

Lemma first_non_scheduler_relation_sched_trace_index_from_none_complete :
  forall task_trace sched_trace t remaining,
    sched_trace_global_fifo_scheduler_relation_check_from
      task_trace sched_trace t remaining = true ->
    first_non_scheduler_relation_sched_trace_index_from
      task_trace sched_trace t remaining = None.
Proof.
  intros task_trace sched_trace t remaining.
  revert t.
  induction remaining as [|entry remaining IH]; simpl; intros t Hcheck.
  - reflexivity.
  - apply Bool.andb_true_iff in Hcheck as [Hrow Hrest].
    rewrite Hrow.
    apply IH.
    exact Hrest.
Qed.

Lemma awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_sound :
  forall task_trace sched_trace,
    awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
      task_trace sched_trace = true ->
    accepted_workload_global_fifo_scheduler_relation_family
      task_trace sched_trace.
Proof.
  intros task_trace sched_trace Haccept.
  unfold awk_workload_accepts_global_fifo_scheduler_relation_sched_trace in Haccept.
  apply Bool.andb_true_iff in Haccept as [Hfamily_policy Hrel].
  apply Bool.andb_true_iff in Hfamily_policy as [Hfamily Hpolicy].
  split.
  - apply awk_workload_accepts_sched_trace_sound.
    exact Hfamily.
  - split.
    + exact Hpolicy.
    + apply sched_trace_global_fifo_scheduler_relation_check_from_sound.
      exact Hrel.
Qed.

Lemma awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_complete :
  forall task_trace sched_trace,
    accepted_workload_global_fifo_scheduler_relation_family
      task_trace sched_trace ->
    awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
      task_trace sched_trace = true.
Proof.
  intros task_trace sched_trace [Hfamily [Hpolicy Hrel]].
  unfold awk_workload_accepts_global_fifo_scheduler_relation_sched_trace.
  unfold sched_trace_global_fifo_scheduler_relation_checkb.
  rewrite (awk_workload_accepts_sched_trace_complete task_trace sched_trace Hfamily).
  rewrite Hpolicy.
  rewrite
    (sched_trace_global_fifo_scheduler_relation_check_from_complete
       task_trace sched_trace 0 sched_trace Hrel).
  reflexivity.
Qed.

Lemma workload_scheduler_facing_choice_empty :
  workload_scheduler_facing_choice empty_sched_trace_entry = [].
Proof.
  reflexivity.
Qed.

Lemma workload_scheduler_facing_choice_head_empty :
  workload_scheduler_facing_choice_head empty_sched_trace_entry = None.
Proof.
  reflexivity.
Qed.

Lemma workload_scheduler_facing_row_state_eq_cpu :
  forall entry c,
    op_current (workload_scheduler_facing_row_state entry) c =
    if c <? 1
    then nth_error (workload_scheduler_facing_choice entry) c
    else None.
Proof.
  intros entry [|c']; unfold workload_scheduler_facing_row_state,
    workload_scheduler_facing_choice; simpl.
  - destruct (sched_trace_primary_current entry) as [j|]; reflexivity.
  - reflexivity.
Qed.

Lemma candidate_source_of_table_nth_error :
  forall table jobs sched t cand,
    nth_error table t = Some cand ->
    candidate_source_of_table table jobs 1 sched t = cand.
Proof.
  intros table jobs sched t.
  revert table.
  induction t as [|t IH]; intros [|x table] cand Hnth; simpl in *.
  - discriminate.
  - inversion Hnth; subst. reflexivity.
  - discriminate.
  - eapply IH. exact Hnth.
Qed.

Lemma candidate_source_of_table_overflow_nil :
  forall table jobs sched t,
    length table <= t ->
    candidate_source_of_table table jobs 1 sched t = [].
Proof.
  intros table jobs sched t Hlen.
  unfold candidate_source_of_table.
  rewrite nth_overflow by lia.
  reflexivity.
Qed.

Lemma choose_top_m_global_fifo_nil :
  forall jobs sched t,
    choose_top_m global_fifo_top_m_spec jobs 1 sched t [] = [].
Proof.
  intros jobs sched t.
  reflexivity.
Qed.

Lemma workload_fifo_candidate_table_contract_canonical :
  forall task_trace sched_trace,
    workload_fifo_candidate_table_contract
      task_trace
      sched_trace
      (workload_fifo_candidate_table task_trace sched_trace).
Proof.
  intros task_trace sched_trace.
  unfold workload_fifo_candidate_table_contract,
    workload_fifo_candidate_table.
  split.
  - rewrite length_map. reflexivity.
  - induction sched_trace as [|entry sched_trace IH]; simpl.
    + constructor.
    + constructor.
      * unfold workload_fifo_candidate_row_contract. reflexivity.
      * exact IH.
Qed.

Lemma workload_fifo_candidate_table_contract_eq :
  forall task_trace sched_trace table,
    workload_fifo_candidate_table_contract task_trace sched_trace table ->
    table = workload_fifo_candidate_table task_trace sched_trace.
Proof.
  intros task_trace sched_trace table [_ Hrows].
  induction Hrows as [|entry cand sched_trace table Hrow _ IH]; simpl.
  - reflexivity.
  - unfold workload_fifo_candidate_row_contract in Hrow.
    subst cand.
    rewrite IH.
    reflexivity.
Qed.

Lemma workload_fifo_candidate_source_matches_relation_candidates :
  forall task_trace sched_trace jobs m sched t,
    candidate_source_of_table
      (workload_fifo_candidate_table task_trace sched_trace)
      jobs m sched t =
    workload_scheduler_relation_candidates
      task_trace
      (nth t sched_trace empty_sched_trace_entry).
Proof.
  intros task_trace sched_trace jobs m sched t.
  revert sched_trace.
  induction t as [|t IH]; intros [|entry sched_trace]; simpl; try reflexivity.
  apply IH.
Qed.

Lemma sched_trace_global_fifo_scheduler_relation_family_from_nth :
  forall task_trace sched_trace remaining t k entry,
    sched_trace_global_fifo_scheduler_relation_family_from
      task_trace sched_trace t remaining ->
    nth_error remaining k = Some entry ->
    workload_global_fifo_scheduler_relation_row
      task_trace sched_trace (t + k) entry.
Proof.
  intros task_trace sched_trace remaining.
  induction remaining as [|row remaining IH];
    intros t k entry Hfamily Hnth; destruct k as [|k]; simpl in Hnth;
  try discriminate.
  - inversion Hnth; subst.
    replace (t + 0) with t by lia.
    exact (proj1 Hfamily).
  - replace (t + S k) with (S t + k) by lia.
    eapply IH.
    + exact (proj2 Hfamily).
    + exact Hnth.
Qed.

Lemma sched_trace_global_fifo_scheduler_relation_family_nth :
  forall task_trace sched_trace t entry,
    sched_trace_global_fifo_scheduler_relation_family task_trace sched_trace ->
    nth_error sched_trace t = Some entry ->
    workload_global_fifo_scheduler_relation_row
      task_trace sched_trace t entry.
Proof.
  intros task_trace sched_trace t entry Hfamily Hnth.
  replace t with (0 + t) by lia.
  eapply sched_trace_global_fifo_scheduler_relation_family_from_nth.
  - exact Hfamily.
  - exact Hnth.
Qed.

Lemma op_struct_inv_two_implies_one :
  forall st,
    op_struct_inv 2 st ->
    op_struct_inv 1 st.
Proof.
  intros st Hinv.
  destruct Hinv as [Hnodup Hrunnable Hcurrent Hdispatch Hdispatch_from].
  constructor.
  - intros j c1 c2 Hlt1 Hlt2.
    eapply Hnodup; lia.
  - exact Hrunnable.
  - exact Hcurrent.
  - intros j c1 c2 Hlt1 Hlt2.
    eapply Hdispatch; lia.
  - intros c j Hlt.
    eapply Hdispatch_from; lia.
Qed.

Definition workload_scheduler_facing_execution_single_worker
    {P : OSLabeledProjection AwkernelState}
    (ex : labeled_concrete_execution P 2)
    : labeled_concrete_execution P 1 :=
  @mkLabeledConcreteExecution
    AwkernelState
    P
    1
    (lce_trace ex)
    (lce_init ex)
    (lce_stepwise ex)
    (fun t => op_struct_inv_two_implies_one _ (lce_struct_inv ex t)).

Lemma workload_scheduler_facing_execution_single_worker_state_eq :
  forall (P : OSLabeledProjection AwkernelState)
         (ex : labeled_concrete_execution P 2)
         t,
    os_to_op_state (osl_to_os_projection P)
      (lce_trace (workload_scheduler_facing_execution_single_worker ex) t) =
    os_to_op_state (osl_to_os_projection P)
      (lce_trace ex t).
Proof.
  reflexivity.
Qed.

Lemma workload_scheduler_facing_cpu_outside_worker_idle :
  forall (P : OSLabeledProjection AwkernelState)
         (ex : labeled_concrete_execution P 2)
         sched_trace t c,
    workload_scheduler_facing_execution_matches_sched_trace ex sched_trace ->
    0 < c ->
    projected_scheduler_relation_schedule ex t c = None.
Proof.
  intros P ex sched_trace t c Hmatch Hgt.
  unfold projected_scheduler_relation_schedule, project_schedule.
  rewrite osl_to_op_trace_unfold.
  rewrite Hmatch.
  rewrite workload_scheduler_facing_row_state_eq_cpu.
  destruct c; [lia|].
  reflexivity.
Qed.

Lemma workload_scheduler_facing_cpu_count_two_eq_one :
  forall (P : OSLabeledProjection AwkernelState)
         (ex : labeled_concrete_execution P 2)
         sched_trace j t,
    workload_scheduler_facing_execution_matches_sched_trace ex sched_trace ->
    cpu_count 2 (projected_scheduler_relation_schedule ex) j t =
    cpu_count 1 (projected_scheduler_relation_schedule ex) j t.
Proof.
  intros P ex sched_trace j t Hmatch.
  simpl.
  unfold runs_on.
  rewrite (workload_scheduler_facing_cpu_outside_worker_idle
             P ex sched_trace t 1 Hmatch ltac:(lia)).
  reflexivity.
Qed.

Lemma workload_scheduler_facing_service_two_eq_one :
  forall (P : OSLabeledProjection AwkernelState)
         (ex : labeled_concrete_execution P 2)
         sched_trace j t,
    workload_scheduler_facing_execution_matches_sched_trace ex sched_trace ->
    service_job 2 (projected_scheduler_relation_schedule ex) j t =
    service_job 1 (projected_scheduler_relation_schedule ex) j t.
Proof.
  intros P ex sched_trace j t Hmatch.
  induction t as [|t IH].
  - reflexivity.
  - rewrite !service_job_unfold.
    rewrite (workload_scheduler_facing_cpu_count_two_eq_one
               P ex sched_trace j t Hmatch).
    rewrite IH by exact Hmatch.
    reflexivity.
Qed.

Lemma workload_scheduler_facing_completed_two_iff_one :
  forall (P : OSLabeledProjection AwkernelState)
         (ex : labeled_concrete_execution P 2)
         jobs sched_trace j t,
    workload_scheduler_facing_execution_matches_sched_trace ex sched_trace ->
    (completed jobs 2 (projected_scheduler_relation_schedule ex) j t <->
     completed jobs 1 (projected_scheduler_relation_schedule ex) j t).
Proof.
  intros P ex jobs sched_trace j t Hmatch.
  unfold completed.
  rewrite (workload_scheduler_facing_service_two_eq_one
             P ex sched_trace j t Hmatch).
  tauto.
Qed.

Lemma workload_scheduler_facing_row_candidate_visible_sound :
  forall row j,
    row_candidate_visibleb row j = true ->
    op_job_visible 1 (workload_scheduler_facing_row_state row) j.
Proof.
  intros row j Hvisible.
  unfold row_candidate_visibleb in Hvisible.
  apply Bool.orb_true_iff in Hvisible.
  destruct Hvisible as [Hvisible | Hdispatch].
  - apply Bool.orb_true_iff in Hvisible.
    destruct Hvisible as [Hcurrent | Hrunnable].
    + left.
      exists 0.
      split; [lia|].
      unfold workload_scheduler_facing_row_state.
      simpl.
      destruct (sched_trace_primary_current row) as [j'|] eqn:Hcur; simpl in Hcurrent; try discriminate.
      apply Nat.eqb_eq in Hcurrent.
      subst j'.
      reflexivity.
    + right. left.
      unfold workload_scheduler_facing_row_state.
      simpl.
      apply job_in_listb_sound.
      exact Hrunnable.
  - right. right.
    exists 0.
    split; [lia|].
    unfold workload_scheduler_facing_row_state.
    simpl.
    destruct (sched_trace_primary_dispatch_target row) as [j'|] eqn:Htarget;
      simpl in Hdispatch; try discriminate.
    apply Nat.eqb_eq in Hdispatch.
    subst j'.
    reflexivity.
Qed.

Lemma workload_scheduler_facing_state_current_inv :
  forall row c j,
    op_current (workload_scheduler_facing_row_state row) c = Some j ->
    c = 0 /\ sched_trace_primary_current row = Some j.
Proof.
  intros row c j Hcur.
  unfold workload_scheduler_facing_row_state in Hcur.
  simpl in Hcur.
  destruct (Nat.eqb c 0) eqn:Hcpu; simpl in Hcur.
  - apply Nat.eqb_eq in Hcpu.
    subst c.
    destruct (sched_trace_primary_current row) as [j'|] eqn:Hentry; inversion Hcur; subst.
    split; reflexivity.
  - discriminate.
Qed.

Lemma workload_scheduler_facing_state_dispatch_inv :
  forall row c j,
    op_dispatch_target (workload_scheduler_facing_row_state row) c = Some j ->
    c = 0 /\ sched_trace_primary_dispatch_target row = Some j.
Proof.
  intros row c j Htarget.
  unfold workload_scheduler_facing_row_state in Htarget.
  simpl in Htarget.
  destruct (Nat.eqb c 0) eqn:Hcpu; simpl in Htarget.
  - apply Nat.eqb_eq in Hcpu.
    subst c.
    destruct (sched_trace_primary_dispatch_target row) as [j'|] eqn:Hentry; inversion Htarget; subst.
    split; reflexivity.
  - discriminate.
Qed.

Lemma option_candidate_includedb_sound :
  forall oj cand j,
    option_candidate_includedb oj cand = true ->
    oj = Some j ->
    In j cand.
Proof.
  intros oj cand j Hinc Hoj.
  unfold option_candidate_includedb in Hinc.
  rewrite Hoj in Hinc.
  apply job_in_listb_sound.
  exact Hinc.
Qed.

Lemma local_projection_sound_single_worker_from_two :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         sched_trace,
    workload_scheduler_facing_execution_matches_sched_trace
      (olac_execution (olcsac_base C))
      sched_trace ->
    local_labeled_concrete_multicore_projection_sound
      jobs
      adm
      1
      (workload_scheduler_facing_execution_single_worker
         (olac_execution (olcsac_base C))).
Proof.
  intros P jobs adm table C sched_trace Hmatch.
  pose proof (olac_sound (olcsac_base C)) as Hsound2.
  pose proof (llcmps_projection_sound Hsound2) as Hproj2.
  refine
    (@mkLocalLabeledConcreteMulticoreProjectionSound
       AwkernelState
       P
       jobs
       adm
       1
       (workload_scheduler_facing_execution_single_worker
          (olac_execution (olcsac_base C)))
       _ _ _).
  - refine
      (@mkLocalLabeledConcreteProjectionSound
         AwkernelState
         P
         jobs
         1
         (workload_scheduler_facing_execution_single_worker
            (olac_execution (olcsac_base C)))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + intros c j Hlt Hcur.
      apply (llcps_init_release Hproj2 c j); [lia|assumption].
    + intros c j Hlt Hcur Hdone.
      pose proof (llcps_init_completion Hproj2 c j ltac:(lia) Hcur) as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j 0 Hmatch)).
      exact Hdone.
    + intros c j Hlt Hcur.
      apply (llcps_init_not_blocked Hproj2 c j); [lia|assumption].
    + exact (llcps_init_runnable_release Hproj2).
    + intros j Hrunnable Hdone.
      pose proof (llcps_init_runnable_completion Hproj2 j Hrunnable) as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j 0 Hmatch)).
      exact Hdone.
    + intros t c j Hlt Hcur.
      apply (llcps_current_origin Hproj2 t c j); [lia|assumption].
    + intros t c j Hlt Hdispatch.
      apply (llcps_dispatch_release Hproj2 t c j); [lia|assumption].
    + intros t c j Hlt Hdispatch.
      apply (llcps_dispatch_not_blocked Hproj2 t c j); [lia|assumption].
    + exact (llcps_wakeup_release Hproj2).
    + intros t j Hwakeup Hdone.
      pose proof (llcps_wakeup_completion Hproj2 t j Hwakeup) as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j (S t) Hmatch)).
      exact Hdone.
    + intros t c j Hlt Hcur1 Hcur2 Hdone.
      pose proof
        (llcps_persistent_completion Hproj2 t c j ltac:(lia) Hcur1 Hcur2)
        as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j (S t) Hmatch)).
      exact Hdone.
    + intros t c j Hlt Hcur1 Hcur2.
      apply (llcps_persistent_not_blocked Hproj2 t c j); [lia|assumption|assumption].
    + intros t c Hlt Hreq.
      apply (llcps_request_sets_need_resched Hproj2 t c); [lia|assumption].
    + intros t c Hlt Hhandle.
      apply (llcps_handle_sets_need_resched Hproj2 t c); [lia|assumption].
    + intros t c j Hlt Hchoose.
      apply (llcps_choose_sets_dispatch_target Hproj2 t c j); [lia|assumption].
    + intros t c j Hlt Hchoose.
      apply (llcps_choose_from_runnable Hproj2 t c j); [lia|assumption].
    + intros t c j Hlt Hdispatch Hdone.
      pose proof
        (llcps_dispatch_completion Hproj2 t c j ltac:(lia) Hdispatch)
        as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j (S t) Hmatch)).
      exact Hdone.
    + exact (llcps_block_clears_current Hproj2).
    + exact (llcps_block_clears_runnable Hproj2).
    + intros t c j Hlt Hblock.
      apply (llcps_block_clears_dispatch_target Hproj2 t c j); [lia|assumption].
    + intros t j Hcomplete.
      pose proof (llcps_complete_sets_completed Hproj2 t j Hcomplete) as Hdone2.
      apply (proj1 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace j (S t) Hmatch)).
      exact Hdone2.
    + intros t c old new Hlt Hpreempt.
      apply (llcps_preempt_release Hproj2 t c old new); [lia|assumption].
    + intros t c old new Hlt Hpreempt Hdone.
      pose proof
        (llcps_preempt_completion Hproj2 t c old new ltac:(lia) Hpreempt)
        as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace new (S t) Hmatch)).
      exact Hdone.
    + intros t c old new Hlt Hpreempt.
      apply (llcps_preempt_not_blocked Hproj2 t c old new); [lia|assumption].
    + intros t c old new Hlt Hpreempt Hdone.
      pose proof
        (llcps_preempt_old_completion Hproj2 t c old new ltac:(lia) Hpreempt)
        as Hdone2.
      apply Hdone2.
      apply (proj2 (workload_scheduler_facing_completed_two_iff_one
                      P (olac_execution (olcsac_base C)) jobs sched_trace old (S t) Hmatch)).
      exact Hdone.
  - intros t c Hge.
    unfold awk_idle_outside_range, op_idle_outside_range.
    change
      (op_current
         (os_to_op_state (osl_to_os_projection P)
            (lce_trace (olac_execution (olcsac_base C)) t)) c = None).
    rewrite (Hmatch t).
    unfold workload_scheduler_facing_row_state.
    simpl.
    destruct c; [lia|].
    reflexivity.
  - intros t c j Hlt Hrun.
    apply (llcmps_placement Hsound2 t c j); [lia|assumption].
Qed.

Lemma workload_candidate_source_sound_single_worker :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         sched_trace,
    workload_candidate_table_contract sched_trace table ->
    workload_scheduler_facing_execution_matches_sched_trace
      (olac_execution (olcsac_base C))
      sched_trace ->
    awk_labeled_concrete_candidate_source_contract
      P
      jobs
      1
      (candidate_source_of_table table)
      (workload_scheduler_facing_execution_single_worker
         (olac_execution (olcsac_base C))).
Proof.
  intros P jobs adm table C sched_trace Htable Hmatch.
  refine
    (@mkLabeledConcreteCandidateSourceContract
       AwkernelState
       P
       jobs
       1
       (candidate_source_of_table table)
       (workload_scheduler_facing_execution_single_worker
          (olac_execution (olcsac_base C)))
       _ _ _ _ _).
  - intros t j Hin.
    assert (Ht : t < length table).
    { eapply candidate_source_of_table_in_bounds.
      exact Hin. }
    assert (Hrow_t : t < length sched_trace).
    { rewrite (proj1 Htable). exact Ht. }
    assert (Hrow :
      nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
    { apply nth_error_nth'. exact Hrow_t. }
    assert (Hcand :
      nth_error table t = Some (nth t table [])).
    { apply nth_error_nth'. exact Ht. }
    pose proof (workload_candidate_table_contract_nth
                  sched_trace table t
                  (nth t sched_trace empty_sched_trace_entry)
                  (nth t table [])
                  Htable Hrow Hcand) as Hrow_contract.
    destruct Hrow_contract as [_ [Hvisible [_ [_ _]]]].
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t).
    rewrite (Hmatch t).
    eapply workload_scheduler_facing_row_candidate_visible_sound.
    eapply all_candidates_visibleb_sound.
    * exact Hvisible.
    * exact Hin.
  - intros t c j Hlt Hcur.
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t) in Hcur.
    rewrite (Hmatch t) in Hcur.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow :
        nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand :
        nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [Hcurrent [_ _]]]].
      destruct (workload_scheduler_facing_state_current_inv
                  (nth t sched_trace empty_sched_trace_entry) c j Hcur)
        as [_ Hentry].
      eapply option_candidate_includedb_sound.
      * exact Hcurrent.
      * exact Hentry.
    + exfalso.
      assert (c = 0) by lia.
      subst c.
      rewrite (nth_overflow sched_trace empty_sched_trace_entry) in Hcur by lia.
      unfold workload_scheduler_facing_row_state in Hcur.
      simpl in Hcur.
      destruct (sched_trace_primary_current empty_sched_trace_entry); discriminate.
  - intros t j Hrunnable.
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t) in Hrunnable.
    rewrite (Hmatch t) in Hrunnable.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow :
        nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand :
        nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [_ [Hrunnable_in _]]]].
      unfold workload_scheduler_facing_row_state in Hrunnable.
      simpl in Hrunnable.
      eapply all_jobs_includedb_sound.
      * exact Hrunnable_in.
      * exact Hrunnable.
    + exfalso.
      rewrite (nth_overflow sched_trace empty_sched_trace_entry) in Hrunnable by lia.
      unfold workload_scheduler_facing_row_state in Hrunnable.
      simpl in Hrunnable.
      contradiction.
  - intros t c j Hlt Hdispatch.
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t) in Hdispatch.
    rewrite (Hmatch t) in Hdispatch.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow :
        nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand :
        nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [_ [_ Hdispatch_in]]]].
      destruct (workload_scheduler_facing_state_dispatch_inv
                  (nth t sched_trace empty_sched_trace_entry) c j Hdispatch)
        as [_ Hentry].
      eapply option_candidate_includedb_sound.
      * exact Hdispatch_in.
      * exact Hentry.
    + exfalso.
      assert (c = 0) by lia.
      subst c.
      rewrite (nth_overflow sched_trace empty_sched_trace_entry) in Hdispatch by lia.
      unfold workload_scheduler_facing_row_state in Hdispatch.
      simpl in Hdispatch.
      destruct (sched_trace_primary_dispatch_target empty_sched_trace_entry); discriminate.
  - intros s1 s2 t Hagree.
    eapply candidate_source_of_table_prefix_extensional.
    exact Hagree.
Qed.

Definition accepted_workload_scheduler_facing_candidate_source_adapter_contract
    (P : OSLabeledProjection AwkernelState)
    jobs adm table
    (C : awk_local_candidate_source_adapter_contract
           P
           (candidate_source_of_table table)
           jobs
           adm
           2)
    sched_trace
    (Htable : workload_candidate_table_contract sched_trace table)
    (Hmatch :
       workload_scheduler_facing_execution_matches_sched_trace
         (olac_execution (olcsac_base C))
         sched_trace)
    : awk_local_candidate_source_adapter_contract
        P
        (candidate_source_of_table table)
        jobs
        adm
        1 :=
  @mkOSLocalCandidateSourceAdapterContract
    AwkernelState
    P
    (candidate_source_of_table table)
    jobs
    adm
    1
    (@mkOSLocalMulticoreAdapterContract
       AwkernelState
       P
       jobs
       adm
       1
       (workload_scheduler_facing_execution_single_worker
          (olac_execution (olcsac_base C)))
       (local_projection_sound_single_worker_from_two
          P jobs adm table C sched_trace Hmatch))
    (workload_candidate_source_sound_single_worker
       P jobs adm table C sched_trace Htable Hmatch).

Lemma accepted_workload_scheduler_facing_sound_from_contract :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm
         table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         task_trace sched_trace,
    accepted_workload_scheduler_facing_family
      task_trace
      jobs
      (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)))
      sched_trace
      table ->
    workload_scheduler_facing_execution_matches_sched_trace
      (olac_execution (olcsac_base C))
      sched_trace ->
    awk_labeled_concrete_single_cpu_scheduler_relation_contract
      P
      jobs
      fifo_generic_spec
      (candidate_source_of_table table)
      (workload_scheduler_facing_execution_single_worker
         (olac_execution (olcsac_base C))).
Proof.
  intros P jobs adm table C task_trace sched_trace
         [_ [Htable [Hlen Hfifo]]] Hmatch.
  refine
    (@mkLabeledConcreteSingleCPUSchedulerRelationContract
       AwkernelState
       P
       jobs
       fifo_generic_spec
       (candidate_source_of_table table)
       (workload_scheduler_facing_execution_single_worker
          (olac_execution (olcsac_base C)))
       _ _).
  - intros t.
    unfold projected_scheduler_relation_schedule, project_schedule.
    rewrite osl_to_op_trace_unfold.
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t).
    rewrite (Hmatch t).
    rewrite workload_scheduler_facing_row_state_eq_cpu.
    unfold workload_scheduler_facing_choice.
    simpl.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hentry :
          nth_error sched_trace t =
          Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Htable_t : t < length table).
      { rewrite <- Hlen. exact Ht. }
      assert (Hcand :
          nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Htable_t. }
      pose proof (Hfifo t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Hentry Hcand) as Hrow.
      unfold workload_global_fifo_row_witness in Hrow.
      unfold projected_candidate_list.
      unfold candidate_source_of_table.
      simpl in Hrow.
      symmetry.
      exact Hrow.
    + rewrite (nth_overflow sched_trace empty_sched_trace_entry) by lia.
      unfold projected_candidate_list.
      assert
        (Hempty :
           candidate_source_of_table table jobs 1
             (project_schedule
                (osl_to_op_trace P
                   (lce_trace
                      (workload_scheduler_facing_execution_single_worker
                         (olac_execution (olcsac_base C))))))
             t = []).
      { unfold candidate_source_of_table.
        rewrite (nth_overflow table []) by (rewrite <- Hlen; lia).
        reflexivity. }
      rewrite Hempty.
      unfold fifo_generic_spec; reflexivity.
  - intros t c Hgt.
    unfold projected_scheduler_relation_schedule, project_schedule.
    rewrite osl_to_op_trace_unfold.
    rewrite (workload_scheduler_facing_execution_single_worker_state_eq
               P (olac_execution (olcsac_base C)) t).
    rewrite (Hmatch t).
    rewrite workload_scheduler_facing_row_state_eq_cpu.
    destruct c; [lia|].
    reflexivity.
Qed.

Definition accepted_workload_scheduler_facing_adapter_contract
    (P : OSLabeledProjection AwkernelState)
    jobs adm table
    (C : awk_local_candidate_source_adapter_contract
           P
           (candidate_source_of_table table)
           jobs
           adm
           2)
    task_trace sched_trace
    (Hfamily :
       accepted_workload_scheduler_facing_family
         task_trace
         jobs
         (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)))
         sched_trace
         table)
    (Hmatch :
       workload_scheduler_facing_execution_matches_sched_trace
         (olac_execution (olcsac_base C))
         sched_trace)
    : awk_local_single_cpu_scheduler_relation_adapter_contract
        P
        fifo_generic_spec
        (candidate_source_of_table table)
        jobs
        adm :=
  @mkOSLocalSingleCPUSchedulerRelationAdapterContract
    AwkernelState
    P
    fifo_generic_spec
    (candidate_source_of_table table)
    jobs
    adm
    (accepted_workload_scheduler_facing_candidate_source_adapter_contract
       P jobs adm table C sched_trace (proj1 (proj2 Hfamily)) Hmatch)
    (accepted_workload_scheduler_facing_sound_from_contract
       P jobs adm table C task_trace sched_trace Hfamily Hmatch).

Definition accepted_workload_scheduler_facing_projected_schedule
    (P : OSLabeledProjection AwkernelState)
    jobs adm table
    (C : awk_local_candidate_source_adapter_contract
           P
           (candidate_source_of_table table)
           jobs
           adm
           2)
    task_trace sched_trace
    (Hfamily :
       accepted_workload_scheduler_facing_family
         task_trace
         jobs
         (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)))
         sched_trace
         table)
    (Hmatch :
       workload_scheduler_facing_execution_matches_sched_trace
         (olac_execution (olcsac_base C))
         sched_trace)
    : Schedule :=
  project_schedule
    (osl_to_op_trace P
       (lce_trace
          (olac_execution
             (olcsac_base
                (olssrac_base
                   (accepted_workload_scheduler_facing_adapter_contract
                      P jobs adm table C task_trace sched_trace Hfamily Hmatch)))))).

Lemma accepted_workload_scheduler_facing_scheduler_rel :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         task_trace sched_trace
         (Hfamily :
            accepted_workload_scheduler_facing_family
              task_trace
              jobs
              (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)))
              sched_trace
              table)
         (Hmatch :
            workload_scheduler_facing_execution_matches_sched_trace
              (olac_execution (olcsac_base C))
              sched_trace),
    scheduler_rel
      (single_cpu_algorithm_schedule fifo_generic_spec (candidate_source_of_table table))
      jobs
      1
      (accepted_workload_scheduler_facing_projected_schedule
         P jobs adm table C task_trace sched_trace Hfamily Hmatch).
Proof.
  intros P jobs adm table C task_trace sched_trace Hfamily Hmatch.
  exact
    (os_local_single_cpu_scheduler_relation_adapter_contract_implies_scheduler_rel
       AwkernelState
       P
       jobs
       adm
       fifo_generic_spec
       (candidate_source_of_table table)
       (accepted_workload_scheduler_facing_adapter_contract
          P jobs adm table C task_trace sched_trace Hfamily Hmatch)).
Qed.

Lemma accepted_workload_scheduler_facing_respects_fifo_policy_at_with :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         task_trace sched_trace t
         (Hfamily :
            accepted_workload_scheduler_facing_family
              task_trace
              jobs
              (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)))
              sched_trace
              table)
         (Hmatch :
            workload_scheduler_facing_execution_matches_sched_trace
              (olac_execution (olcsac_base C))
              sched_trace),
    respects_algorithm_spec_at_with
      fifo_policy
      jobs
      (candidate_source_of_table table)
      (accepted_workload_scheduler_facing_projected_schedule
         P jobs adm table C task_trace sched_trace Hfamily Hmatch)
      t.
Proof.
  intros P jobs adm table C task_trace sched_trace t Hfamily Hmatch.
  exact
    (os_local_single_cpu_scheduler_relation_adapter_contract_respects_algorithm_spec_at_with
       AwkernelState
       P
       jobs
       adm
       fifo_generic_spec
       fifo_policy
       (candidate_source_of_table table)
       t
       (accepted_workload_scheduler_facing_adapter_contract
          P jobs adm table C task_trace sched_trace Hfamily Hmatch)
       choose_fifo_refines_fifo_policy).
Qed.

Lemma awk_workload_accepts_scheduler_facing_family_from_checker_acceptance :
  forall task_trace sched_trace jobs sched table,
    awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
      task_trace sched_trace = true ->
    workload_candidate_table_contract sched_trace table ->
    workload_global_fifo_table_witness jobs sched sched_trace table ->
    accepted_workload_scheduler_facing_family
      task_trace jobs sched sched_trace table.
Proof.
  intros task_trace sched_trace jobs sched table Haccept Htable Hfifo.
  pose proof
    (awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_sound
       task_trace sched_trace Haccept)
    as [Haccepted _].
  split.
  - exact Haccepted.
  - split; assumption.
Qed.

Lemma awk_workload_checker_acceptance_global_fifo_scheduler_rel_from_fifo_table :
  forall task_trace sched_trace table,
    awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
      task_trace sched_trace = true ->
    workload_fifo_candidate_table_contract task_trace sched_trace table ->
    scheduler_rel
      (top_m_algorithm_schedule global_fifo_top_m_spec
         (candidate_source_of_table table))
      (workload_scheduler_relation_jobs task_trace sched_trace)
      1
      (workload_scheduler_relation_schedule task_trace sched_trace).
Proof.
  intros task_trace sched_trace table Haccept Htable.
  pose proof
    (awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_sound
       task_trace sched_trace Haccept)
    as [_ [_ Hrelation]].
  pose proof
    (workload_fifo_candidate_table_contract_eq
       task_trace sched_trace table Htable) as Htable_eq.
  subst table.
  unfold top_m_algorithm_schedule.
  simpl.
  intros t c.
  unfold workload_scheduler_relation_schedule.
  destruct (c <? 1) eqn:Hcpu; [|reflexivity].
  rewrite workload_fifo_candidate_source_matches_relation_candidates.
  destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
  - assert
      (Hentry :
         nth_error sched_trace t =
         Some (nth t sched_trace empty_sched_trace_entry)).
    { apply nth_error_nth'. exact Ht. }
    pose proof
      (sched_trace_global_fifo_scheduler_relation_family_nth
         task_trace
         sched_trace
         t
         (nth t sched_trace empty_sched_trace_entry)
         Hrelation
         Hentry) as Hrow.
    unfold workload_global_fifo_scheduler_relation_row in Hrow.
    rewrite <- Hrow.
    reflexivity.
  - rewrite nth_overflow by lia.
    reflexivity.
Qed.

Lemma awk_workload_checker_acceptance_global_fifo_scheduler_rel :
  forall task_trace sched_trace,
    awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
      task_trace sched_trace = true ->
    scheduler_rel
      (top_m_algorithm_schedule global_fifo_top_m_spec
      (candidate_source_of_table
            (workload_fifo_candidate_table task_trace sched_trace)))
      (workload_scheduler_relation_jobs task_trace sched_trace)
      1
      (workload_scheduler_relation_schedule task_trace sched_trace).
Proof.
  intros task_trace sched_trace Haccept.
  eapply awk_workload_checker_acceptance_global_fifo_scheduler_rel_from_fifo_table.
  - exact Haccept.
  - apply workload_fifo_candidate_table_contract_canonical.
Qed.

Lemma awk_workload_checker_acceptance_scheduler_rel :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         task_trace sched_trace
         (Haccept :
            awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
              task_trace sched_trace = true)
         (Htrace :
            workload_trace_matches_execution
              (olac_execution (olcsac_base C))
              task_trace
              sched_trace)
         (Hmatch :
            workload_scheduler_facing_execution_matches_sched_trace
              (olac_execution (olcsac_base C))
              sched_trace)
         (Htable : workload_candidate_table_contract sched_trace table)
         (Hfifo :
            workload_global_fifo_table_witness
              jobs
              (projected_scheduler_relation_schedule
                 (olac_execution (olcsac_base C)))
              sched_trace
              table),
    let Hfamily :=
      awk_workload_accepts_scheduler_facing_family_from_checker_acceptance
        task_trace
        sched_trace
        jobs
        (projected_scheduler_relation_schedule
           (olac_execution (olcsac_base C)))
        table
        Haccept
        Htable
        Hfifo in
    scheduler_rel
      (single_cpu_algorithm_schedule fifo_generic_spec (candidate_source_of_table table))
      jobs
      1
      (accepted_workload_scheduler_facing_projected_schedule
         P jobs adm table C task_trace sched_trace Hfamily Hmatch).
Proof.
  intros P jobs adm table C task_trace sched_trace
         Haccept Htrace Hmatch Htable Hfifo.
  pose proof
    (workload_trace_matches_execution_sched
       P (olac_execution (olcsac_base C)) task_trace sched_trace Htrace)
    as _.
  exact
    (accepted_workload_scheduler_facing_scheduler_rel
       P
       jobs
       adm
       table
       C
       task_trace
       sched_trace
       (awk_workload_accepts_scheduler_facing_family_from_checker_acceptance
          task_trace
          sched_trace
          jobs
          (projected_scheduler_relation_schedule
             (olac_execution (olcsac_base C)))
          table
          Haccept
          Htable
          Hfifo)
       Hmatch).
Qed.

Lemma awk_workload_checker_acceptance_respects_fifo_policy_at_with :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm table
         (C : awk_local_candidate_source_adapter_contract
                P
                (candidate_source_of_table table)
                jobs
                adm
                2)
         task_trace sched_trace t
         (Haccept :
            awk_workload_accepts_global_fifo_scheduler_relation_sched_trace
              task_trace sched_trace = true)
         (Htrace :
            workload_trace_matches_execution
              (olac_execution (olcsac_base C))
              task_trace
              sched_trace)
         (Hmatch :
            workload_scheduler_facing_execution_matches_sched_trace
              (olac_execution (olcsac_base C))
              sched_trace)
         (Htable : workload_candidate_table_contract sched_trace table)
         (Hfifo :
            workload_global_fifo_table_witness
              jobs
              (projected_scheduler_relation_schedule
                 (olac_execution (olcsac_base C)))
              sched_trace
              table),
    let Hfamily :=
      awk_workload_accepts_scheduler_facing_family_from_checker_acceptance
        task_trace
        sched_trace
        jobs
        (projected_scheduler_relation_schedule
           (olac_execution (olcsac_base C)))
        table
        Haccept
        Htable
        Hfifo in
    respects_algorithm_spec_at_with
      fifo_policy
      jobs
      (candidate_source_of_table table)
      (accepted_workload_scheduler_facing_projected_schedule
         P jobs adm table C task_trace sched_trace Hfamily Hmatch)
      t.
Proof.
  intros P jobs adm table C task_trace sched_trace t
         Haccept Htrace Hmatch Htable Hfifo.
  pose proof
    (workload_trace_matches_execution_task_wf
       P (olac_execution (olcsac_base C)) task_trace sched_trace Htrace)
    as _.
  exact
    (accepted_workload_scheduler_facing_respects_fifo_policy_at_with
       P
       jobs
       adm
       table
       C
       task_trace
       sched_trace
       t
       (awk_workload_accepts_scheduler_facing_family_from_checker_acceptance
          task_trace
          sched_trace
          jobs
          (projected_scheduler_relation_schedule
             (olac_execution (olcsac_base C)))
          table
          Haccept
          Htable
          Hfifo)
       Hmatch).
Qed.
