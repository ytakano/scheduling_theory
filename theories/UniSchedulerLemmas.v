(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import SchedulerValidity.
Require Import DispatcherRefinement.
Require Import UniSchedulerInterface.
Import ListNotations.

(* ===== 1. Derive schedulers from a UniSchedulerBundle ===== *)

(* The concrete (executable) single-CPU scheduler for a bundle.
   Converts usb_spec to GenericDispatchSpec via HasGenericDispatchSpec,
   then wraps via single_cpu_dispatch_scheduler_on. *)
Definition uni_scheduler_on
    {J : JobId -> Prop}
    {Spec : Type}
    `{HSpec : HasGenericDispatchSpec Spec}
    (B : UniSchedulerBundle J Spec)
    : Scheduler :=
  single_cpu_dispatch_scheduler_on J
    (to_generic_dispatch_spec B.(usb_spec))
    B.(usb_candidates)
    B.(usb_candidates_ok).

(* The abstract policy scheduler for a bundle.
   Wraps usb_policy + usb_candidates via single_cpu_policy_scheduler. *)
Definition uni_policy_scheduler_on
    {J : JobId -> Prop}
    {Spec : Type}
    `{HSpec : HasGenericDispatchSpec Spec}
    (B : UniSchedulerBundle J Spec)
    : Scheduler :=
  single_cpu_policy_scheduler B.(usb_policy) B.(usb_candidates).

(* ===== 2. Validity ===== *)

(* Any schedule satisfying the concrete scheduler is a valid schedule. *)
Lemma uni_scheduler_on_valid :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericDispatchSpec Spec}
           (B : UniSchedulerBundle J Spec) jobs sched,
      scheduler_rel (uni_scheduler_on B) jobs 1 sched ->
      valid_schedule jobs 1 sched.
Proof.
  intros J Spec HSpec B jobs sched Hrel.
  exact (single_cpu_dispatch_valid
           (to_generic_dispatch_spec B.(usb_spec))
           B.(usb_candidates) jobs sched Hrel).
Qed.

(* ===== 3. Refinement ===== *)

(* If a schedule satisfies the concrete scheduler, it also satisfies the
   abstract policy scheduler.  The bridge is usb_refines. *)
Lemma uni_scheduler_on_refines_policy :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericDispatchSpec Spec}
           (B : UniSchedulerBundle J Spec) jobs sched,
      scheduler_rel (uni_scheduler_on B) jobs 1 sched ->
      scheduler_rel (uni_policy_scheduler_on B) jobs 1 sched.
Proof.
  intros J Spec HSpec B jobs sched Hrel.
  exact (single_cpu_dispatch_schedule_implies_single_cpu_policy_schedule
           (to_generic_dispatch_spec B.(usb_spec))
           B.(usb_policy) B.(usb_candidates) jobs sched
           B.(usb_refines) Hrel).
Qed.

(* ===== 4. schedulable_by_on intro via bundle ===== *)

(* Standard entry point: from a feasible witness schedule, derive
   schedulable_by_on for the concrete scheduler. *)
Lemma uni_scheduler_on_schedulable_by_on_intro :
    forall (J : JobId -> Prop) (Spec : Type) `{HSpec : HasGenericDispatchSpec Spec}
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

