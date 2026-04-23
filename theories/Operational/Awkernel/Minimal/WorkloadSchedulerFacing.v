From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerRelationContract.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateTable.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateSource.
From RocqSched Require Import Multicore.Global.GlobalFIFO.

Definition workload_scheduler_facing_row_state
    (entry : AwkernelSchedTraceEntry) : OpState :=
  mkOpState
    (fun c => if Nat.eqb c 0 then aste_current entry else None)
    (aste_runnable entry)
    (fun c => if Nat.eqb c 0 then aste_need_resched entry else false)
    (fun c => if Nat.eqb c 0 then aste_dispatch_target entry else None).

Definition workload_scheduler_facing_choice
    (entry : AwkernelSchedTraceEntry) : list JobId :=
  match aste_current entry with
  | Some j => [j]
  | None => []
  end.

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
  choose_top_m global_fifo_top_m_spec jobs 2 sched t cand =
  workload_scheduler_facing_choice entry.

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

Lemma workload_scheduler_facing_choice_empty :
  workload_scheduler_facing_choice empty_sched_trace_entry = [].
Proof.
  reflexivity.
Qed.

Lemma workload_scheduler_facing_row_state_eq_cpu :
  forall entry c,
    op_current (workload_scheduler_facing_row_state entry) c =
    if c <? 2
    then nth_error (workload_scheduler_facing_choice entry) c
    else None.
Proof.
  intros entry [|[|c']]; unfold workload_scheduler_facing_row_state,
    workload_scheduler_facing_choice; simpl.
  - destruct (aste_current entry) as [j|]; reflexivity.
  - destruct (aste_current entry) as [j|]; reflexivity.
  - reflexivity.
Qed.

Lemma candidate_source_of_table_nth_error :
  forall table jobs sched t cand,
    nth_error table t = Some cand ->
    candidate_source_of_table table jobs 2 sched t = cand.
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
    candidate_source_of_table table jobs 2 sched t = [].
Proof.
  intros table jobs sched t Hlen.
  unfold candidate_source_of_table.
  rewrite nth_overflow by lia.
  reflexivity.
Qed.

Lemma choose_top_m_global_fifo_nil :
  forall jobs sched t,
    choose_top_m global_fifo_top_m_spec jobs 2 sched t [] = [].
Proof.
  intros jobs sched t.
  reflexivity.
Qed.

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
    awk_labeled_concrete_top_m_scheduler_relation_contract
      P
      jobs
      2
      global_fifo_top_m_spec
      (candidate_source_of_table table)
      (olac_execution (olcsac_base C)).
Proof.
  intros P jobs adm table C task_trace sched_trace
         [_ [_ [Hlen Hfifo]]] Hmatch.
  refine
    (@mkLabeledConcreteTopMSchedulerRelationContract
       AwkernelState
       P
       jobs
       2
       global_fifo_top_m_spec
       (candidate_source_of_table table)
       (olac_execution (olcsac_base C))
       _).
  intros t c.
  destruct c as [|[|c']].
  - change
      (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)) t 0 =
       nth_error
         (choose_top_m global_fifo_top_m_spec jobs 2
            (projected_scheduler_relation_schedule (olac_execution (olcsac_base C))) t
            (candidate_source_of_table table jobs 2
               (projected_scheduler_relation_schedule (olac_execution (olcsac_base C))) t)) 0).
    unfold projected_scheduler_relation_schedule, project_schedule.
    rewrite osl_to_op_trace_unfold.
    rewrite (Hmatch t).
    rewrite workload_scheduler_facing_row_state_eq_cpu.
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
      unfold projected_scheduler_relation_schedule in Hrow.
      pose proof (f_equal (fun l => nth_error l 0) Hrow) as Hnth.
      unfold candidate_source_of_table.
      change
        (nth_error
           (workload_scheduler_facing_choice
              (nth t sched_trace empty_sched_trace_entry)) 0 =
         nth_error
           (choose_top_m global_fifo_top_m_spec jobs 2
              (project_schedule
                 (osl_to_op_trace P (lce_trace (olac_execution (olcsac_base C)))))
              t
              (nth t table [])) 0).
      symmetry.
      exact Hnth.
    + rewrite (nth_overflow sched_trace empty_sched_trace_entry) by lia.
      rewrite workload_scheduler_facing_choice_empty.
      unfold candidate_source_of_table.
      rewrite (nth_overflow table []) by (rewrite <- Hlen; lia).
      reflexivity.
  - change
      (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)) t 1 =
       nth_error
         (choose_top_m global_fifo_top_m_spec jobs 2
            (projected_scheduler_relation_schedule (olac_execution (olcsac_base C))) t
            (candidate_source_of_table table jobs 2
               (projected_scheduler_relation_schedule (olac_execution (olcsac_base C))) t)) 1).
    unfold projected_scheduler_relation_schedule, project_schedule.
    rewrite osl_to_op_trace_unfold.
    rewrite (Hmatch t).
    rewrite workload_scheduler_facing_row_state_eq_cpu.
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
      unfold projected_scheduler_relation_schedule in Hrow.
      pose proof (f_equal (fun l => nth_error l 1) Hrow) as Hnth.
      unfold candidate_source_of_table.
      change
        (nth_error
           (workload_scheduler_facing_choice
              (nth t sched_trace empty_sched_trace_entry)) 1 =
         nth_error
           (choose_top_m global_fifo_top_m_spec jobs 2
              (project_schedule
                 (osl_to_op_trace P (lce_trace (olac_execution (olcsac_base C)))))
              t
              (nth t table [])) 1).
      symmetry.
      exact Hnth.
    + rewrite (nth_overflow sched_trace empty_sched_trace_entry) by lia.
      rewrite workload_scheduler_facing_choice_empty.
      unfold candidate_source_of_table.
      rewrite (nth_overflow table []) by (rewrite <- Hlen; lia).
      reflexivity.
  - change
      (projected_scheduler_relation_schedule (olac_execution (olcsac_base C)) t (S (S c')) = None).
    unfold projected_scheduler_relation_schedule, project_schedule.
    rewrite osl_to_op_trace_unfold.
    rewrite (Hmatch t).
    rewrite workload_scheduler_facing_row_state_eq_cpu.
    unfold candidate_source_of_table.
    destruct (lt_dec t (length table)) as [Hlt | Hge].
    + reflexivity.
    + rewrite nth_overflow by lia.
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
    : awk_local_top_m_scheduler_relation_adapter_contract
        P
        global_fifo_top_m_spec
        (candidate_source_of_table table)
        jobs
        adm
        2 :=
  @mkOSLocalTopMSchedulerRelationAdapterContract
    AwkernelState
    P
    global_fifo_top_m_spec
    (candidate_source_of_table table)
    jobs
    adm
    2
    C
    (accepted_workload_scheduler_facing_sound_from_contract
       P jobs adm table C task_trace sched_trace Hfamily Hmatch).
