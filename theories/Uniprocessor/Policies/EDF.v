From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Common.MetricChooser.
Import ListNotations.

(* ===== Phase 1: EDF Metric and Choose Function ===== *)

(* EDF metric: the absolute deadline of job j, as a Z for use with MetricChooser. *)
Definition edf_metric (jobs : JobId -> Job) (j : JobId) : Z :=
  Z.of_nat (job_abs_deadline (jobs j)).

(* EDF choose function:
   From candidates, filter to those that are eligible, then select
   the one with the earliest (minimum) absolute deadline. *)
Definition choose_edf (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                       (t : Time) (candidates : list JobId) : option JobId :=
  choose_min_metric (edf_metric jobs) jobs m sched t candidates.

(* ===== Phase 2: EDF Choose Correctness ===== *)

(* If no candidate is eligible, choose_edf returns None. *)
Lemma choose_edf_none_if_no_eligible : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_edf jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  exact (choose_min_metric_none_if_no_eligible _ jobs m sched t candidates Hnone).
Qed.

(* Theorem 1: The chosen job is eligible. *)
Theorem choose_edf_eligible : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hchoose.
  exact (choose_min_metric_eligible _ jobs m sched t candidates j Hchoose).
Qed.

(* Theorem 2: The chosen job has the minimum deadline among all eligible candidates. *)
Theorem choose_edf_min_deadline : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    eligible jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Hchoose j' Hin Helig.
  pose proof (choose_min_metric_min (edf_metric jobs) jobs m sched t candidates j
                Hchoose j' Hin Helig) as H.
  unfold edf_metric in H. lia.
Qed.

(* Theorem 3: A job is always chosen when an eligible candidate exists. *)
Theorem choose_edf_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates Hex.
  exact (choose_min_metric_some_if_exists _ jobs m sched t candidates Hex).
Qed.

(* The chosen job is always a member of the candidate list. *)
Lemma choose_edf_in_candidates : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j -> In j candidates.
Proof.
  intros jobs m sched t candidates j Hchoose.
  exact (choose_min_metric_in_candidates _ jobs m sched t candidates j Hchoose).
Qed.

(* ===== Phase 3: Explicit Precondition Lemmas ===== *)

(* B1: If candidates exactly represents the eligible set and an eligible job exists,
   choose_edf always returns Some. *)
Lemma choose_edf_complete : forall jobs m sched t candidates,
    (forall j, eligible jobs m sched j t <-> In j candidates) ->
    (exists j, eligible jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates Href Hex.
  exact (choose_min_metric_complete _ jobs m sched t candidates Href Hex).
Qed.

(* B2: If candidates exactly represents the eligible set, the chosen job has
   minimum deadline in the entire eligible set. *)
Lemma choose_edf_optimal : forall jobs m sched t candidates j,
    (forall j', eligible jobs m sched j' t <-> In j' candidates) ->
    choose_edf jobs m sched t candidates = Some j ->
    forall j', eligible jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Href Hchoose j' Helig.
  pose proof (choose_min_metric_optimal (edf_metric jobs) jobs m sched t candidates j
                Href Hchoose j' Helig) as H.
  unfold edf_metric in H. lia.
Qed.

(* ===== Phase 4: Uniqueness / Determinism ===== *)

(* A2: If job j has strictly smaller deadline than every other eligible candidate,
   EDF is forced to return j. *)
Lemma choose_edf_unique_min : forall jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    (forall j', In j' candidates -> eligible jobs m sched j' t ->
                j' <> j ->
                job_abs_deadline (jobs j) < job_abs_deadline (jobs j')) ->
    choose_edf jobs m sched t candidates = Some j.
Proof.
  intros jobs m sched t candidates j Hin Helig Hstrict.
  apply (choose_min_metric_unique_min (edf_metric jobs) jobs m sched t candidates j Hin Helig).
  intros j' Hin' Helig' Hneq.
  unfold edf_metric. pose proof (Hstrict j' Hin' Helig' Hneq). lia.
Qed.

(* ===== Phase 5: EDF satisfies GenericSchedulingAlgorithm and EDFSchedulerSpec ===== *)

(* EDF satisfies the generic (policy-independent) scheduling algorithm interface. *)
Definition edf_generic_spec : GenericSchedulingAlgorithm :=
  mkGenericSchedulingAlgorithm
    choose_edf
    choose_edf_eligible
    choose_edf_some_if_exists
    choose_edf_none_if_no_eligible
    choose_edf_in_candidates.

(* EDF-specific scheduler spec: extends GenericSchedulingAlgorithm with the
   minimum-deadline invariant.  This is the full EDF interface. *)
Record EDFSchedulerSpec : Type := mkEDFSchedulerSpec {
  (* Sub-record coercion: an EDFSchedulerSpec can be used where a
     GenericSchedulingAlgorithm is expected. *)
  edf_generic :> GenericSchedulingAlgorithm ;

  (* EDF policy invariant: the chosen job has the minimum absolute deadline
     among all eligible candidates. *)
  edf_choose_min_deadline :
    forall jobs m sched t candidates j,
      choose edf_generic jobs m sched t candidates = Some j ->
      forall j', In j' candidates ->
      eligible jobs m sched j' t ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j') ;
}.

(* EDF is a concrete instance of EDFSchedulerSpec. *)
Definition edf_scheduler_spec : EDFSchedulerSpec :=
  mkEDFSchedulerSpec
    edf_generic_spec
    choose_edf_min_deadline.

(* ===== Phase 6: EDF-specific lemmas (policy invariant consequences) ===== *)

Section EDFSchedulerLemmasSection.

  Variable spec        : EDFSchedulerSpec.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* A5: the chosen job has minimum absolute deadline among all eligible candidates. *)
  Lemma edf_choose_some_implies_min_deadline :
      forall j j',
        spec.(choose) jobs m sched t candidates = Some j ->
        In j' candidates ->
        eligible jobs m sched j' t ->
        job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Helig.
    exact (spec.(edf_choose_min_deadline) jobs m sched t candidates j Hchoose j' Hin Helig).
  Qed.

  (* C1: no eligible candidate has strictly smaller deadline than the chosen job. *)
  Lemma edf_choose_some_implies_no_earlier_deadline_candidate :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        ~exists j', In j' candidates /\ eligible jobs m sched j' t /\
                    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
  Proof.
    intros j Hchoose [j' [Hin [Helig Hlt]]].
    pose proof (edf_choose_some_implies_min_deadline j j' Hchoose Hin Helig) as Hle.
    lia.
  Qed.

  (* C2: if an eligible candidate has deadline <= chosen deadline, they are equal. *)
  Lemma edf_choose_some_tie_deadline :
      forall j j',
        spec.(choose) jobs m sched t candidates = Some j ->
        In j' candidates ->
        eligible jobs m sched j' t ->
        job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) ->
        job_abs_deadline (jobs j) = job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Helig Hle.
    pose proof (edf_choose_some_implies_min_deadline j j' Hchoose Hin Helig) as Hle2.
    lia.
  Qed.

End EDFSchedulerLemmasSection.

(* Lift edf_generic_spec into a Scheduler relation for the single-CPU case.
   candidates_of supplies the candidate list at each time step. *)
Definition edf_scheduler
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  single_cpu_algorithm_schedule edf_generic_spec candidates_of.

(* ===== Phase 7: Abstract EDF policy ===== *)

(* Auxiliary: if choose_edf returns None, all candidates are ineligible.
   (Converse of choose_edf_none_if_no_eligible.) *)
Lemma choose_edf_none_implies_no_eligible : forall jobs m sched t candidates,
    choose_edf jobs m sched t candidates = None ->
    forall j, In j candidates -> ~eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates Hnone j Hin Helig.
  assert (Hsome : exists j', choose_edf jobs m sched t candidates = Some j').
  { apply choose_edf_some_if_exists. exists j. split. exact Hin. exact Helig. }
  destruct Hsome as [j' Hsome]. rewrite Hnone in Hsome. discriminate.
Qed.

(* Abstract EDF policy: ties are permitted (any job with minimum deadline wins).
   - None: all candidates are ineligible.
   - Some j: j is in the list, eligible, and has minimum deadline among
     all eligible candidates. *)
Definition edf_policy : SchedulingAlgorithmSpec :=
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
          job_abs_deadline (jobs j) <= job_abs_deadline (jobs j')
    end.

Lemma edf_policy_sane : SchedulingAlgorithmSpecSanity edf_policy.
Proof.
  constructor.
  - intros jobs m sched t candidates j Hpol.
    exact (proj1 Hpol).
  - intros jobs m sched t candidates j Hpol.
    exact (proj1 (proj2 Hpol)).
Qed.

Lemma choose_edf_refines_edf_policy :
  algorithm_refines_spec edf_generic_spec edf_policy.
Proof.
  unfold algorithm_refines_spec.
  intros jobs m sched t candidates.
  unfold edf_policy. simpl.
  destruct (choose_edf jobs m sched t candidates) as [j|] eqn:Hchoose.
  - split.
    + exact (choose_edf_in_candidates jobs m sched t candidates j Hchoose).
    + split.
      * exact (choose_edf_eligible jobs m sched t candidates j Hchoose).
      * intros j' Hin Helig.
        exact (choose_edf_min_deadline jobs m sched t candidates j Hchoose j' Hin Helig).
  - intros j Hin Helig.
    exact (choose_edf_none_implies_no_eligible jobs m sched t candidates Hchoose j Hin Helig).
Qed.

(* ===== Phase 8: UniSchedulerBundle instance for EDF ===== *)

From RocqSched Require Import Uniprocessor.Core.UniSchedulerInterface.
From RocqSched Require Import Uniprocessor.Core.UniSchedulerLemmas.

(* EDFSchedulerSpec maps to GenericSchedulingAlgorithm via the edf_generic field. *)
#[global]
Instance HasGenericSchedulingAlgorithm_EDFSchedulerSpec
    : HasGenericSchedulingAlgorithm EDFSchedulerSpec := {
  to_generic_scheduling_algorithm := edf_generic
}.

(* Bundle that packages all EDF components into the standard UniSchedulerBundle
   interface.  Spec is EDFSchedulerSpec, carrying the min-deadline invariant.
   Client supplies the candidate source; the rest is fixed to EDF. *)
Definition edf_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J EDFSchedulerSpec :=
  mkUniSchedulerBundle
    candidates_of
    edf_scheduler_spec
    cand_spec
    edf_policy
    edf_policy_sane
    choose_edf_refines_edf_policy.

(* Thin wrapper: concrete single-CPU EDF scheduler from a bundle. *)
Definition edf_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_scheduler_on (edf_bundle J candidates_of cand_spec).

(* Thin wrapper: abstract EDF policy scheduler from a bundle. *)
Definition edf_policy_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_policy_scheduler_on (edf_bundle J candidates_of cand_spec).
