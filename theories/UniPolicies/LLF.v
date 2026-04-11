(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulerValidity.
Require Import SchedulingAlgorithmRefinement.
Require Import UniPolicies.MetricChooser.
Import ListNotations.

(* ===== Phase 1: LLF Metric and Dispatch Function ===== *)

(* The LLF metric: the laxity of job j at time t under schedule sched. *)
Definition llf_metric
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (j : JobId) : Z :=
  laxity jobs m sched j t.

(* LLF dispatch function:
   From candidates, filter to those that are eligible, then select
   the one with the minimum laxity. *)
Definition choose_llf
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : option JobId :=
  choose_min_metric (llf_metric jobs m sched t) jobs m sched t candidates.

(* ===== Phase 2: GenericSchedulingAlgorithm Correctness ===== *)

(* Theorem 1: The chosen job is eligible. *)
Lemma choose_llf_eligible : forall jobs m sched t candidates j,
    choose_llf jobs m sched t candidates = Some j ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hchoose.
  exact (choose_min_metric_eligible _ jobs m sched t candidates j Hchoose).
Qed.

(* Theorem 2: A job is always chosen when an eligible candidate exists. *)
Lemma choose_llf_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_llf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates Hex.
  exact (choose_min_metric_some_if_exists _ jobs m sched t candidates Hex).
Qed.

(* Theorem 3: If no candidate is eligible, returns None. *)
Lemma choose_llf_none_if_no_eligible : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_llf jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  exact (choose_min_metric_none_if_no_eligible _ jobs m sched t candidates Hnone).
Qed.

(* Theorem 4: The chosen job is always a member of the candidate list. *)
Lemma choose_llf_in_candidates : forall jobs m sched t candidates j,
    choose_llf jobs m sched t candidates = Some j -> In j candidates.
Proof.
  intros jobs m sched t candidates j Hchoose.
  exact (choose_min_metric_in_candidates _ jobs m sched t candidates j Hchoose).
Qed.

(* ===== Phase 3: LLF Satisfies GenericSchedulingAlgorithm ===== *)

Definition llf_generic_spec : GenericSchedulingAlgorithm :=
  mkGenericSchedulingAlgorithm
    choose_llf
    choose_llf_eligible
    choose_llf_some_if_exists
    choose_llf_none_if_no_eligible
    choose_llf_in_candidates.

(* ===== Phase 4: LLF-Specific Optimality Lemma ===== *)

(* The chosen job has minimum laxity among all eligible candidates. *)
Theorem choose_llf_min_laxity : forall jobs m sched t candidates j,
    choose_llf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    eligible jobs m sched j' t ->
    (laxity jobs m sched j t <= laxity jobs m sched j' t)%Z.
Proof.
  intros jobs m sched t candidates j Hchoose j' Hin Helig.
  exact (choose_min_metric_min _ jobs m sched t candidates j Hchoose j' Hin Helig).
Qed.

(* ===== Phase 5: Abstract LLF Policy ===== *)

(* Abstract LLF policy: the chosen job has the minimum laxity
   among all eligible candidates.
   - None: all candidates are ineligible.
   - Some j: j is in the list, eligible, and has minimum laxity. *)
Definition llf_policy : SchedulingAlgorithmSpec :=
  fun jobs m sched t candidates oj =>
    match oj with
    | None =>
        forall j, In j candidates -> ~eligible jobs m sched j t
    | Some j =>
        In j candidates /\
        eligible jobs m sched j t /\
        forall j',
          In j' candidates ->
          eligible jobs m sched j' t ->
          (laxity jobs m sched j t <= laxity jobs m sched j' t)%Z
    end.

Lemma llf_policy_sane : SchedulingAlgorithmSpecSanity llf_policy.
Proof.
  constructor.
  - intros jobs m sched t candidates j Hpol.
    exact (proj1 Hpol).
  - intros jobs m sched t candidates j Hpol.
    exact (proj1 (proj2 Hpol)).
Qed.

(* Auxiliary: if choose_llf returns None, all candidates are ineligible. *)
Lemma choose_llf_none_implies_no_eligible : forall jobs m sched t candidates,
    choose_llf jobs m sched t candidates = None ->
    forall j, In j candidates -> ~eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates Hnone j Hin Helig.
  assert (Hsome : exists j', choose_llf jobs m sched t candidates = Some j').
  { apply choose_llf_some_if_exists. exists j. split. exact Hin. exact Helig. }
  destruct Hsome as [j' Hsome].
  rewrite Hnone in Hsome. discriminate.
Qed.

Lemma choose_llf_refines_llf_policy :
  algorithm_refines_spec llf_generic_spec llf_policy.
Proof.
  unfold algorithm_refines_spec.
  intros jobs m sched t candidates.
  unfold llf_policy. simpl.
  destruct (choose_llf jobs m sched t candidates) as [j|] eqn:Hchoose.
  - split.
    + exact (choose_llf_in_candidates jobs m sched t candidates j Hchoose).
    + split.
      * exact (choose_llf_eligible jobs m sched t candidates j Hchoose).
      * intros j' Hin Helig.
        exact (choose_llf_min_laxity jobs m sched t candidates j Hchoose j' Hin Helig).
  - intros j Hin Helig.
    exact (choose_llf_none_implies_no_eligible jobs m sched t candidates Hchoose j Hin Helig).
Qed.

(* ===== Phase 6: LLF-Specific Scheduler Spec ===== *)

(* LLF-specific scheduler spec: extends GenericSchedulingAlgorithm with the
   minimum-laxity invariant. *)
Record LLFSchedulerSpec : Type := mkLLFSchedulerSpec {
  llf_generic :> GenericSchedulingAlgorithm ;
  llf_choose_min_laxity :
    forall jobs m sched t candidates j,
      dispatch llf_generic jobs m sched t candidates = Some j ->
      forall j', In j' candidates ->
      eligible jobs m sched j' t ->
      (laxity jobs m sched j t <= laxity jobs m sched j' t)%Z ;
}.

Definition llf_scheduler_spec : LLFSchedulerSpec :=
  mkLLFSchedulerSpec
    llf_generic_spec
    choose_llf_min_laxity.

(* ===== Phase 7: UniSchedulerBundle instance for LLF ===== *)

Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.

#[global]
Instance HasGenericSchedulingAlgorithm_LLFSchedulerSpec
    : HasGenericSchedulingAlgorithm LLFSchedulerSpec := {
  to_generic_scheduling_algorithm := llf_generic
}.

(* Bundle that packages all LLF components into the standard UniSchedulerBundle
   interface.  Spec is LLFSchedulerSpec, carrying the min-laxity invariant.
   Client supplies the candidate source; the rest is fixed to LLF. *)
Definition llf_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J LLFSchedulerSpec :=
  mkUniSchedulerBundle
    candidates_of
    llf_scheduler_spec
    cand_spec
    llf_policy
    llf_policy_sane
    choose_llf_refines_llf_policy.

(* Thin wrapper: concrete single-CPU LLF scheduler from a bundle. *)
Definition llf_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_scheduler_on (llf_bundle J candidates_of cand_spec).

(* Thin wrapper: abstract LLF policy scheduler from a bundle. *)
Definition llf_policy_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_policy_scheduler_on (llf_bundle J candidates_of cand_spec).

(* Legacy-style constructor for direct scheduler_rel use, mirroring edf_scheduler. *)
Definition llf_scheduler
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  single_cpu_algorithm_schedule llf_generic_spec candidates_of.
