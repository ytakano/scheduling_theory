(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
Import ListNotations.

(* ===== HasGenericSchedulingAlgorithm typeclass ===== *)

(* A typeclass that maps a scheduler-specific spec type to the common
   GenericSchedulingAlgorithm interface.  This lets UniSchedulerBundle hold a
   rich spec (e.g., EDFSchedulerSpec with the min-deadline invariant)
   while the generic machinery still works through GenericSchedulingAlgorithm. *)
Class HasGenericSchedulingAlgorithm (Spec : Type) := {
  to_generic_scheduling_algorithm : Spec -> GenericSchedulingAlgorithm
}.

(* Identity instance: GenericSchedulingAlgorithm is its own projection. *)
#[global]
Instance HasGenericSchedulingAlgorithm_GenericSchedulingAlgorithm
    : HasGenericSchedulingAlgorithm GenericSchedulingAlgorithm := {
  to_generic_scheduling_algorithm := fun s => s
}.

(* ===== UniSchedulerBundle ===== *)

(* UniSchedulerBundle: the minimal package needed to build a verified single-CPU
   scheduler from a concrete choose function and an abstract policy.

   The Spec type parameter lets callers carry a richer spec (e.g., EDFSchedulerSpec)
   in usb_spec while converting to GenericSchedulingAlgorithm via HasGenericSchedulingAlgorithm.

   Fields:
     usb_candidates     — how to generate the candidate job list at each time step
     usb_spec           — concrete choose spec (of type Spec)
     usb_candidates_ok  — soundness/completeness/prefix-extensionality of candidates
     usb_alg_spec         — abstract choose policy (SchedulingAlgorithmSpec)
     usb_alg_spec_sane    — minimum health conditions for the abstract policy
     usb_algorithm_refines        — the concrete scheduling algorithm refines the abstract scheduling algorithm spec

   Design notes:
     - validity is NOT a field: derivable from usb_spec + usb_candidates_ok
       via single_cpu_algorithm_valid (see UniSchedulerLemmas).
     - usb_algorithm_refines IS a field: policy-specific proof; where EDF/FIFO/RR differ.  *)
Record UniSchedulerBundle
    (J : JobId -> Prop)
    (Spec : Type)
    `{HSpec : HasGenericSchedulingAlgorithm Spec} : Type := mkUniSchedulerBundle {
  usb_candidates    : CandidateSource ;
  usb_spec          : Spec ;
  usb_candidates_ok : CandidateSourceSpec J usb_candidates ;
  usb_alg_spec        : SchedulingAlgorithmSpec ;
  usb_alg_spec_sane   : SchedulingAlgorithmSpecSanity usb_alg_spec ;
  usb_algorithm_refines       :
    algorithm_refines_spec (to_generic_scheduling_algorithm usb_spec) usb_alg_spec
}.

Arguments mkUniSchedulerBundle {J Spec HSpec}.
Arguments usb_candidates    {J Spec HSpec}.
Arguments usb_spec          {J Spec HSpec}.
Arguments usb_candidates_ok {J Spec HSpec}.
Arguments usb_alg_spec        {J Spec HSpec}.
Arguments usb_alg_spec_sane   {J Spec HSpec}.
Arguments usb_algorithm_refines       {J Spec HSpec}.

