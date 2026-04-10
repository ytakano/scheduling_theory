(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import SchedulerValidity.
Require Import DispatcherRefinement.
Import ListNotations.

(* ===== HasGenericDispatchSpec typeclass ===== *)

(* A typeclass that maps a scheduler-specific spec type to the common
   GenericDispatchSpec interface.  This lets UniSchedulerBundle hold a
   rich spec (e.g., EDFSchedulerSpec with the min-deadline invariant)
   while the generic machinery still works through GenericDispatchSpec. *)
Class HasGenericDispatchSpec (Spec : Type) := {
  to_generic_dispatch_spec : Spec -> GenericDispatchSpec
}.

(* Identity instance: GenericDispatchSpec is its own projection. *)
#[global]
Instance HasGenericDispatchSpec_GenericDispatchSpec
    : HasGenericDispatchSpec GenericDispatchSpec := {
  to_generic_dispatch_spec := fun s => s
}.

(* ===== UniSchedulerBundle ===== *)

(* UniSchedulerBundle: the minimal package needed to build a verified single-CPU
   scheduler from a concrete dispatch function and an abstract policy.

   The Spec type parameter lets callers carry a richer spec (e.g., EDFSchedulerSpec)
   in usb_spec while converting to GenericDispatchSpec via HasGenericDispatchSpec.

   Fields:
     usb_candidates     — how to generate the candidate job list at each time step
     usb_spec           — concrete dispatch spec (of type Spec)
     usb_candidates_ok  — soundness/completeness/prefix-extensionality of candidates
     usb_policy         — abstract dispatch policy (DispatchPolicy)
     usb_policy_sane    — minimum health conditions for the abstract policy
     usb_refines        — the concrete dispatcher refines the abstract policy

   Design notes:
     - validity is NOT a field: derivable from usb_spec + usb_candidates_ok
       via single_cpu_dispatch_valid (see UniSchedulerLemmas).
     - usb_refines IS a field: policy-specific proof; where EDF/FIFO/RR differ.  *)
Record UniSchedulerBundle
    (J : JobId -> Prop)
    (Spec : Type)
    `{HSpec : HasGenericDispatchSpec Spec} : Type := mkUniSchedulerBundle {
  usb_candidates    : CandidateSource ;
  usb_spec          : Spec ;
  usb_candidates_ok : CandidateSourceSpec J usb_candidates ;
  usb_policy        : DispatchPolicy ;
  usb_policy_sane   : PolicySanity usb_policy ;
  usb_refines       :
    dispatcher_refines_policy (to_generic_dispatch_spec usb_spec) usb_policy
}.

Arguments mkUniSchedulerBundle {J Spec HSpec}.
Arguments usb_candidates    {J Spec HSpec}.
Arguments usb_spec          {J Spec HSpec}.
Arguments usb_candidates_ok {J Spec HSpec}.
Arguments usb_policy        {J Spec HSpec}.
Arguments usb_policy_sane   {J Spec HSpec}.
Arguments usb_refines       {J Spec HSpec}.

