(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
Import ListNotations.

(* ===== 1. SchedulingAlgorithmSpec type ===== *)

(* A choose policy relates the execution context (job map, CPU count,
   schedule-so-far, time, candidate list) to the selected job (or None).
   This single type covers EDF, FIFO, RR, fixed-priority, etc. *)
Definition SchedulingAlgorithmSpec :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId -> Prop.

(* ===== 2. SchedulingAlgorithmSpecSanity ===== *)

(* Minimum health conditions for a SchedulingAlgorithmSpec: only governs the Some branch.
   The None branch is intentionally unconstrained to leave room for work-conserving
   vs. non-work-conserving policies and future extensions. *)
Record SchedulingAlgorithmSpecSanity (policy : SchedulingAlgorithmSpec) : Prop := mkSchedulingAlgorithmSpecSanity {
  (* If the policy selects j, then j is in the candidate list. *)
  policy_some_in_candidates :
    forall jobs m sched t candidates j,
      policy jobs m sched t candidates (Some j) ->
      In j candidates ;

  (* If the policy selects j, then j is eligible at time t. *)
  policy_some_eligible :
    forall jobs m sched t candidates j,
      policy jobs m sched t candidates (Some j) ->
      eligible jobs m sched j t
}.

(* ===== 3. Policy-validity predicates ===== *)

(* The schedule's selection at time t on CPU 0 satisfies the policy,
   given an explicit candidate list. *)
Definition respects_algorithm_spec_at
    (policy : SchedulingAlgorithmSpec)
    (jobs : JobId -> Job)
    (m : nat)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  policy jobs m sched t candidates (sched t 0).

(* Same as respects_algorithm_spec_at but uses a CandidateSource function. *)
Definition respects_algorithm_spec_at_with
    (policy : SchedulingAlgorithmSpec)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  policy jobs 1 sched t (candidates_of jobs 1 sched t) (sched t 0).

(* The schedule respects the policy at every time step before horizon H. *)
Definition respects_algorithm_spec_before
    (policy : SchedulingAlgorithmSpec)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    respects_algorithm_spec_at_with policy jobs candidates_of sched t.

(* ===== 4. Policy-valid schedule / scheduler ===== *)

(* A schedule satisfies single_cpu_algorithm_spec_schedule when it uses exactly 1 CPU
   and every time step respects the policy. *)
Definition single_cpu_algorithm_spec_schedule
    (policy : SchedulingAlgorithmSpec)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (m : nat)
    (sched : Schedule) : Prop :=
  m = 1 /\
  forall t, respects_algorithm_spec_at_with policy jobs candidates_of sched t.

(* Lift to a Scheduler record. *)
Definition single_cpu_algorithm_spec_scheduler
    (policy : SchedulingAlgorithmSpec)
    (candidates_of : CandidateSource)
    : Scheduler :=
  mkScheduler (single_cpu_algorithm_spec_schedule policy candidates_of).

(* ===== 5. Generic inspection lemmas ===== *)

(* Lemma A: the selected job is in the candidate list. *)
Lemma respects_algorithm_spec_at_with_in_candidates :
  forall policy
         (Hsane : SchedulingAlgorithmSpecSanity policy)
         jobs candidates_of sched t j,
    respects_algorithm_spec_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    In j (candidates_of jobs 1 sched t).
Proof.
  intros policy Hsane jobs candidates_of sched t j Hresp Hrun.
  unfold respects_algorithm_spec_at_with in Hresp.
  rewrite Hrun in Hresp.
  destruct Hsane as [Hin_cand _].
  exact (Hin_cand jobs 1 sched t _ j Hresp).
Qed.

(* Lemma B: the selected job is eligible. *)
Lemma respects_algorithm_spec_at_with_implies_eligible :
  forall policy
         (Hsane : SchedulingAlgorithmSpecSanity policy)
         jobs candidates_of sched t j,
    respects_algorithm_spec_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    eligible jobs 1 sched j t.
Proof.
  intros policy Hsane jobs candidates_of sched t j Hresp Hrun.
  unfold respects_algorithm_spec_at_with in Hresp.
  rewrite Hrun in Hresp.
  destruct Hsane as [_ Helig_cand].
  exact (Helig_cand jobs 1 sched t _ j Hresp).
Qed.

(* Lemma C: combined with CandidateSourceSpec, the selected job belongs to J. *)
Lemma respects_algorithm_spec_at_with_in_subset :
  forall policy
         (Hsane : SchedulingAlgorithmSpecSanity policy)
         J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    respects_algorithm_spec_at_with policy jobs candidates_of sched t ->
    sched t 0 = Some j ->
    J j.
Proof.
  intros policy Hsane J candidates_of cand_spec jobs sched t j Hresp Hrun.
  destruct cand_spec as [Hsound _ _].
  apply (Hsound jobs 1 sched t j).
  exact (respects_algorithm_spec_at_with_in_candidates policy Hsane jobs candidates_of
           sched t j Hresp Hrun).
Qed.

(* Lemma D: build schedulable_by_on directly from a policy-valid witness schedule. *)
Lemma single_cpu_algorithm_spec_schedulable_by_on_intro :
  forall J policy candidates_of jobs sched,
    single_cpu_algorithm_spec_schedule policy candidates_of jobs 1 sched ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    schedulable_by_on J (single_cpu_algorithm_spec_scheduler policy candidates_of) jobs 1.
Proof.
  intros J policy candidates_of jobs sched Hpol Hvalid Hfeas.
  apply (schedulable_by_on_intro J (single_cpu_algorithm_spec_scheduler policy candidates_of)
           jobs 1 sched).
  - exact Hpol.
  - exact Hvalid.
  - exact Hfeas.
Qed.
