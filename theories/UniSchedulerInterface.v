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

(* UniSchedulerBundle: the minimal package needed to build a verified single-CPU
   scheduler from a concrete dispatch function and an abstract policy.

   Fields:
     usb_candidates     — how to generate the candidate job list at each time step
     usb_candidates_ok  — soundness/completeness/prefix-extensionality of candidates
     usb_spec           — concrete dispatch function (GenericDispatchSpec)
     usb_policy         — abstract dispatch policy (DispatchPolicy)
     usb_policy_sane    — minimum health conditions for the abstract policy
     usb_refinement     — the concrete dispatcher refines the abstract policy

   Design notes:
     - validity is NOT a field: it can be derived from usb_spec + usb_candidates_ok
       by single_cpu_dispatch_valid (see UniSchedulerLemmas).
     - refinement IS a field: this is where the policy-specific proof lives and
       where EDF, FIFO, RR, etc. differ from each other.                       *)
Record UniSchedulerBundle (J : JobId -> Prop) : Type := mkUniSchedulerBundle {
  usb_candidates    : CandidateSource ;
  usb_candidates_ok : CandidateSourceSpec J usb_candidates ;
  usb_spec          : GenericDispatchSpec ;
  usb_policy        : DispatchPolicy ;
  usb_policy_sane   : PolicySanity usb_policy ;
  usb_refinement    : dispatcher_refines_policy usb_spec usb_policy
}.

Arguments usb_candidates    {J}.
Arguments usb_candidates_ok {J}.
Arguments usb_spec          {J}.
Arguments usb_policy        {J}.
Arguments usb_policy_sane   {J}.
Arguments usb_refinement    {J}.
