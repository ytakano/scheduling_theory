From Stdlib Require Import List Bool Arith Arith.PeanoNat.
Require Import Base.
Require Import Schedule.
Import ListNotations.

(* Abstract specification for a single-CPU scheduler dispatch function.
   A concrete scheduler (e.g. EDF) satisfies this spec by instantiating
   the record fields with the corresponding proven lemmas.

   This interface enables Partitioned.v to abstract over the per-CPU policy:
   any scheduler satisfying UniSchedulerSpec can be composed into a
   partitioned multiprocessor schedule. *)

Record UniSchedulerSpec : Type := mkUniSchedulerSpec {
  (* The dispatch function: given a job map, CPU count, schedule, time,
     and a list of candidate jobs, return the chosen job (if any). *)
  choose : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId ;

  (* Spec 1: the chosen job is ready at time t. *)
  choose_ready :
    forall jobs m sched t candidates j,
      choose jobs m sched t candidates = Some j ->
      ready jobs m sched j t ;

  (* Spec 2: the chosen job has minimum deadline among all ready candidates. *)
  choose_min_deadline :
    forall jobs m sched t candidates j,
      choose jobs m sched t candidates = Some j ->
      forall j', In j' candidates ->
      ready jobs m sched j' t ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j') ;

  (* Spec 3: if a ready candidate exists, the dispatcher returns Some. *)
  choose_some_if_ready :
    forall jobs m sched t candidates,
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      exists j', choose jobs m sched t candidates = Some j' ;

  (* Spec 4: if no candidate is ready, the dispatcher returns None. *)
  choose_none_if_no_ready :
    forall jobs m sched t candidates,
      (forall j, In j candidates -> ~ready jobs m sched j t) ->
      choose jobs m sched t candidates = None ;
}.
