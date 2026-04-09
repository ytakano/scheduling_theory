From Stdlib Require Import List Bool Arith Arith.PeanoNat.
Require Import Base.
Require Import Schedule.
Import ListNotations.

(* Generic dispatch specification for a single-CPU scheduler.
   Any concrete scheduler (FIFO, RR, prioritized FIFO, EDF, …) can satisfy
   this interface.  Policy-specific invariants (e.g. EDF's choose_min_deadline)
   are defined in the policy's own file (see EDF.v for EDFSchedulerSpec).

   This interface is the basis for Partitioned.v: any per-CPU policy that
   satisfies GenericDispatchSpec can be composed into a partitioned
   multiprocessor schedule. *)

Record GenericDispatchSpec : Type := mkGenericDispatchSpec {
  (* The dispatch function: given a job map, CPU count, schedule, time,
     and a list of candidate jobs, return the chosen job (if any). *)
  dispatch : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId ;

  (* Spec 1: the chosen job is ready at time t. *)
  dispatch_ready :
    forall jobs m sched t candidates j,
      dispatch jobs m sched t candidates = Some j ->
      ready jobs m sched j t ;

  (* Spec 2: if a ready candidate exists, the dispatcher returns Some. *)
  dispatch_some_if_ready :
    forall jobs m sched t candidates,
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      exists j', dispatch jobs m sched t candidates = Some j' ;

  (* Spec 3: if no candidate is ready, the dispatcher returns None. *)
  dispatch_none_if_no_ready :
    forall jobs m sched t candidates,
      (forall j, In j candidates -> ~ready jobs m sched j t) ->
      dispatch jobs m sched t candidates = None ;

  (* Spec 4: the chosen job is always a member of the candidate list. *)
  dispatch_in_candidates :
    forall jobs m sched t candidates j,
      dispatch jobs m sched t candidates = Some j ->
      In j candidates ;
}.
