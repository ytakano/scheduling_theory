(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulerValidity.
Import ListNotations.

(* ===== 1. Dispatcher Refinement ===== *)

(* A concrete dispatcher (GenericSchedulingAlgorithm) refines an abstract policy when
   every output of the dispatcher is permitted by the policy, for all inputs.
   This connects the "executable" world (dispatch functions) to the
   "specification" world (SchedulingAlgorithmSpec predicates). *)
Definition algorithm_refines_spec
    (spec : GenericSchedulingAlgorithm)
    (policy : SchedulingAlgorithmSpec) : Prop :=
  forall jobs m sched t candidates,
    policy jobs m sched t candidates
      (spec.(dispatch) jobs m sched t candidates).

(* ===== 2. Dispatcher-generated schedules respect the policy ===== *)

(* If a concrete dispatcher refines a policy, then any schedule produced by
   single_cpu_algorithm_schedule respects the policy at every time step. *)
Lemma single_cpu_algorithm_schedule_respects_algorithm_spec_at_with :
  forall spec policy candidates_of jobs sched t,
    algorithm_refines_spec spec policy ->
    scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
    respects_algorithm_spec_at_with policy jobs candidates_of sched t.
Proof.
  intros spec policy candidates_of jobs sched t Href Hrel.
  unfold respects_algorithm_spec_at_with.
  destruct Hrel as [_ Hrel].
  destruct (Hrel t) as [Heq _].
  rewrite Heq.
  exact (Href jobs 1 sched t (candidates_of jobs 1 sched t)).
Qed.

(* Horizon variant: respects the policy at every time step before H. *)
Lemma single_cpu_algorithm_schedule_respects_algorithm_spec_before :
  forall spec policy candidates_of jobs sched H,
    algorithm_refines_spec spec policy ->
    scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
    respects_algorithm_spec_before policy jobs candidates_of sched H.
Proof.
  intros spec policy candidates_of jobs sched H Href Hrel.
  unfold respects_algorithm_spec_before.
  intros t _.
  exact (single_cpu_algorithm_schedule_respects_algorithm_spec_at_with
           spec policy candidates_of jobs sched t Href Hrel).
Qed.

(* ===== 3. Scheduler relation inclusion ===== *)

(* A dispatcher-based schedule also satisfies single_cpu_algorithm_spec_schedule. *)
Lemma single_cpu_algorithm_schedule_implies_single_cpu_algorithm_spec_schedule :
  forall spec policy candidates_of jobs sched,
    algorithm_refines_spec spec policy ->
    scheduler_rel (single_cpu_algorithm_schedule spec candidates_of) jobs 1 sched ->
    single_cpu_algorithm_spec_schedule policy candidates_of jobs 1 sched.
Proof.
  intros spec policy candidates_of jobs sched Href Hrel.
  unfold single_cpu_algorithm_spec_schedule.
  split.
  - exact (proj1 Hrel).
  - intros t.
    exact (single_cpu_algorithm_schedule_respects_algorithm_spec_at_with
             spec policy candidates_of jobs sched t Href Hrel).
Qed.
