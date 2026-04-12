From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
Import ListNotations.

(* Generic scheduling algorithm interface for a single-CPU scheduler.
   Any concrete scheduler (FIFO, RR, prioritized FIFO, EDF, …) can satisfy
   this interface.  Policy-specific invariants (e.g. EDF's choose_min_deadline)
   are defined in the policy's own file (see EDF.v for EDFSchedulerSpec).

   Design notes:
   - `candidates` is a "candidate set": it does NOT require every member to be
     eligible.  The scheduling algorithm simply ignores ineligible candidates.  Callers
     are responsible for ensuring that every job they want to schedule is
     eventually included in the candidate list (the "completeness" contract).
   - Subset / finite-set reasoning (which jobs belong to the system, which CPU
     owns which jobs, etc.) is handled by the bridge layer in
     SchedulingAlgorithmSchedulerBridge.v, not here.
   - Do NOT add job-set predicates (J, CandidateSourceSpec, etc.) to this
     interface; doing so would force every policy (EDF, FIFO, RR, …) to carry
     unwanted dependencies. *)

Record GenericSchedulingAlgorithm : Type := mkGenericSchedulingAlgorithm {
  (* The choose function: given a job map, CPU count, schedule, time,
     and a list of candidate jobs, return the chosen job (if any).
     The list may contain ineligible jobs; the scheduling algorithm skips them. *)
  choose : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId ;

  (* Spec 1: the chosen job is eligible at time t. *)
  choose_eligible :
    forall jobs m sched t candidates j,
      choose jobs m sched t candidates = Some j ->
      eligible jobs m sched j t ;

  (* Spec 2: if an eligible candidate exists, the choose function returns Some.
     Note: the candidate list may also contain ineligible jobs. *)
  choose_some_if_eligible_candidate :
    forall jobs m sched t candidates,
      (exists j, In j candidates /\ eligible jobs m sched j t) ->
      exists j', choose jobs m sched t candidates = Some j' ;

  (* Spec 3: if no candidate is eligible, the choose function returns None. *)
  choose_none_if_no_eligible_candidate :
    forall jobs m sched t candidates,
      (forall j, In j candidates -> ~eligible jobs m sched j t) ->
      choose jobs m sched t candidates = None ;

  (* Spec 4: the chosen job is always a member of the candidate list. *)
  choose_in_candidates :
    forall jobs m sched t candidates j,
      choose jobs m sched t candidates = Some j ->
      In j candidates ;
}.
