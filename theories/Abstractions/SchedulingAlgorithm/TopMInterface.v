(* TopMInterface.v
   Generic interface for scheduling algorithms that choose up to m jobs
   simultaneously — the multicore analogue of GenericSchedulingAlgorithm.

   GenericTopMSchedulingAlgorithm
   --------------------------------
   choose_top_m         : returns a list of at most m chosen jobs
   choose_top_m_nodup   : the returned list has no duplicates
   choose_top_m_in_candidates : every returned job was in the candidate list
   choose_top_m_eligible      : every returned job is eligible
   choose_top_m_length_le_m   : the list has at most m elements
   choose_top_m_complete_if_room : if an eligible candidate is missing from
                                   the result, the result already has m jobs
*)

From Stdlib Require Import List Arith Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
Import ListNotations.

Record GenericTopMSchedulingAlgorithm : Type :=
  mkGenericTopMSchedulingAlgorithm {

    (** The core selector: given jobs, CPU count m, a schedule, a time, and
        a list of candidate job IDs, returns a list of chosen job IDs. *)
    choose_top_m :
      (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> list JobId ;

    (** No job appears twice in the result. *)
    choose_top_m_nodup :
      forall jobs m sched t candidates,
        NoDup (choose_top_m jobs m sched t candidates) ;

    (** Every job in the result was among the candidates. *)
    choose_top_m_in_candidates :
      forall jobs m sched t candidates j,
        In j (choose_top_m jobs m sched t candidates) ->
        In j candidates ;

    (** Every job in the result is eligible at time t. *)
    choose_top_m_eligible :
      forall jobs m sched t candidates j,
        In j (choose_top_m jobs m sched t candidates) ->
        eligible jobs m sched j t ;

    (** The result contains at most m jobs. *)
    choose_top_m_length_le_m :
      forall jobs m sched t candidates,
        length (choose_top_m jobs m sched t candidates) <= m ;

    (** If an eligible candidate is not in the result, the result is full
        (i.e., the scheduler chose as many jobs as there are CPUs). *)
    choose_top_m_complete_if_room :
      forall jobs m sched t candidates j,
        In j candidates ->
        eligible jobs m sched j t ->
        ~ In j (choose_top_m jobs m sched t candidates) ->
        length (choose_top_m jobs m sched t candidates) = m

  }.
