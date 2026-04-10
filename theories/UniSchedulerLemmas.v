(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulerValidity.
Require Import SchedulingAlgorithmRefinement.
Require Import UniSchedulerInterface.
Import ListNotations.

(* ===== 1. Derive schedulers from a UniSchedulerBundle ===== *)

(* The concrete (executable) single-CPU scheduler for a bundle.
   Converts usb_spec to GenericSchedulingAlgorithm via HasGenericSchedulingAlgorithm,
   then wraps via single_cpu_algorithm_scheduler_on. *)
Definition uni_scheduler_on
    {J : JobId -> Prop}
    {Spec : Type}
    `{HSpec : HasGenericSchedulingAlgorithm Spec}
    (B : UniSchedulerBundle J Spec)
    : Scheduler :=
  single_cpu_algorithm_scheduler_on J
    (to_generic_scheduling_algorithm B.(usb_spec))
    B.(usb_candidates)
    B.(usb_candidates_ok).

(* The abstract policy scheduler for a bundle.
   Wraps usb_alg_spec + usb_candidates via single_cpu_algorithm_spec_scheduler. *)
Definition uni_policy_scheduler_on
    {J : JobId -> Prop}
    {Spec : Type}
    `{HSpec : HasGenericSchedulingAlgorithm Spec}
    (B : UniSchedulerBundle J Spec)
    : Scheduler :=
  single_cpu_algorithm_spec_scheduler B.(usb_alg_spec) B.(usb_candidates).

(* ===== 2. Validity ===== *)

(* Any schedule satisfying the concrete scheduler is a valid schedule. *)
Lemma uni_scheduler_on_valid :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericSchedulingAlgorithm Spec}
           (B : UniSchedulerBundle J Spec) jobs sched,
      scheduler_rel (uni_scheduler_on B) jobs 1 sched ->
      valid_schedule jobs 1 sched.
Proof.
  intros J Spec HSpec B jobs sched Hrel.
  exact (single_cpu_algorithm_valid
           (to_generic_scheduling_algorithm B.(usb_spec))
           B.(usb_candidates) jobs sched Hrel).
Qed.

(* ===== 3. Refinement ===== *)

(* If a schedule satisfies the concrete scheduler, it also satisfies the
   abstract policy scheduler.  The bridge is usb_algorithm_refines. *)
Lemma uni_scheduler_on_refines_policy :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericSchedulingAlgorithm Spec}
           (B : UniSchedulerBundle J Spec) jobs sched,
      scheduler_rel (uni_scheduler_on B) jobs 1 sched ->
      scheduler_rel (uni_policy_scheduler_on B) jobs 1 sched.
Proof.
  intros J Spec HSpec B jobs sched Hrel.
  exact (single_cpu_algorithm_schedule_implies_single_cpu_algorithm_spec_schedule
           (to_generic_scheduling_algorithm B.(usb_spec))
           B.(usb_alg_spec) B.(usb_candidates) jobs sched
           B.(usb_algorithm_refines) Hrel).
Qed.

(* ===== 4. schedulable_by_on intro via bundle ===== *)

(* Standard entry point: from a feasible witness schedule, derive
   schedulable_by_on for the concrete scheduler. *)
Lemma uni_scheduler_on_schedulable_by_on_intro :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericSchedulingAlgorithm Spec}
           (B : UniSchedulerBundle J Spec) jobs sched,
      scheduler_rel (uni_scheduler_on B) jobs 1 sched ->
      feasible_schedule_on J jobs 1 sched ->
      schedulable_by_on J (uni_scheduler_on B) jobs 1.
Proof.
  intros J Spec HSpec B jobs sched Hrel Hfeas.
  exact (schedulable_by_on_intro J (uni_scheduler_on B) jobs 1 sched
           Hrel
           (uni_scheduler_on_valid J Spec B jobs sched Hrel)
           Hfeas).
Qed.

