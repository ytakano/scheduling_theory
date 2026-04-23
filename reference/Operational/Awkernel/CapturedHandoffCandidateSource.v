From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Refinement.OSCandidateSourceTheorem.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
From RocqSched Require Import Operational.Awkernel.HandoffTrace.
From RocqSched Require Import Operational.Awkernel.CapturedHandoffTrace.

(** * Candidate-source witness for the captured Awkernel handoff trace

    This module records the smallest adapter-local candidate source needed to
    reuse the common candidate-source theorems over the current captured
    handoff witness. It intentionally stops at the local
    [os_local_candidate_source_adapter_contract] boundary and does not attempt
    to package [CandidateSourceSpec], scheduler-relation, or algorithm-level
    reuse. *)

Definition awk_captured_handoff_candidates : CandidateSource :=
  fun _jobs _m _sched t =>
    match t with
    | 0 => []
    | 1 => [1]
    | 2 => [1]
    | 3 => [1]
    | 4 => [1]
    | 5 => [1]
    | _ => []
    end.

Definition awk_captured_handoff_projected_candidates (t : Time) : list JobId :=
  projected_candidate_list
    awk_baseline_jobs
    2
    awk_captured_handoff_contract_execution
    awk_captured_handoff_candidates
    t.

Lemma awk_captured_handoff_visible_job1 :
  forall t,
    1 <= t <= 5 ->
    op_job_visible
      2
      (os_to_op_state (osl_to_os_projection awk_captured_handoff_projection)
         (lce_trace awk_captured_handoff_contract_execution t))
      1.
Proof.
  intros t Hrange.
  destruct t as [|[|[|[|[|[|t']]]]]]; try lia.
  - right. left. simpl. auto.
  - right. left. simpl. auto.
  - right. left. simpl. auto.
  - right. left. simpl. auto.
  - left. exists 1. split; [lia|simpl; reflexivity].
Qed.

Lemma awk_captured_handoff_candidate_source_sound :
  @labeled_concrete_candidate_source_contract
    AwkernelHandoffState
    awk_captured_handoff_projection
    awk_baseline_jobs
    2
    awk_captured_handoff_candidates
    awk_captured_handoff_contract_execution.
Proof.
  refine
    {| lccsc_candidates_visible := _;
       lccsc_current_in_candidates := _;
       lccsc_runnable_in_candidates := _;
       lccsc_dispatch_target_in_candidates := _;
       lccsc_prefix_extensional := _ |}.
  - intros t j Hin.
    destruct t as [|[|[|[|[|[|t']]]]]]; simpl in Hin; try contradiction.
    all: destruct Hin as [Hj | []]; subst j.
    all: apply awk_captured_handoff_visible_job1; lia.
  - intros t c j Hlt Hcur.
    rewrite awk_captured_handoff_trace_eq in Hcur.
    destruct t as [|[|[|[|[|[|t']]]]]].
    + simpl in Hcur. discriminate.
    + simpl in Hcur. discriminate.
    + simpl in Hcur. discriminate.
    + simpl in Hcur. discriminate.
    + simpl in Hcur. discriminate.
    + destruct c as [|[|c']].
      * simpl in Hcur. discriminate.
      * inversion Hcur; subst j. simpl. auto.
      * lia.
    + simpl in Hcur. discriminate.
  - intros t j Hin.
    rewrite awk_captured_handoff_trace_eq in Hin.
    destruct t as [|[|[|[|[|[|t']]]]]].
    + simpl in Hin. contradiction.
    + simpl in Hin. destruct Hin as [Hj | []]. subst j. simpl. auto.
    + simpl in Hin. destruct Hin as [Hj | []]. subst j. simpl. auto.
    + simpl in Hin. destruct Hin as [Hj | []]. subst j. simpl. auto.
    + simpl in Hin. destruct Hin as [Hj | []]. subst j. simpl. auto.
    + simpl in Hin. contradiction.
    + simpl in Hin. contradiction.
  - intros t c j Hlt Htarget.
    rewrite awk_captured_handoff_trace_eq in Htarget.
    destruct t as [|[|[|[|[|[|t']]]]]].
    + simpl in Htarget. discriminate.
    + simpl in Htarget. discriminate.
    + simpl in Htarget. discriminate.
    + simpl in Htarget. discriminate.
    + destruct c as [|[|c']].
      * simpl in Htarget. discriminate.
      * inversion Htarget; subst j. simpl. auto.
      * lia.
    + simpl in Htarget. discriminate.
    + simpl in Htarget. discriminate.
  - intros s1 s2 t Hprefix.
    reflexivity.
Qed.

Definition awk_captured_handoff_candidate_adapter_contract :
  @os_local_candidate_source_adapter_contract
    AwkernelHandoffState
    awk_captured_handoff_projection
    awk_captured_handoff_candidates
    awk_baseline_jobs
    awk_baseline_admissibility
    2 :=
  {|
    olcsac_base := awk_captured_handoff_contract;
    olcsac_candidates := awk_captured_handoff_candidate_source_sound;
  |}.

Example awk_captured_handoff_choose_job_is_a_candidate :
  In 1 (awk_captured_handoff_projected_candidates 3).
Proof.
  unfold awk_captured_handoff_projected_candidates, projected_candidate_list,
         awk_captured_handoff_candidates.
  simpl. auto.
Qed.
