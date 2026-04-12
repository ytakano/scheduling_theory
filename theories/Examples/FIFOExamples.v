From Stdlib Require Import List Bool Arith.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import UniPolicies.FIFO.
Import ListNotations.

(* Concrete examples for the FIFO choose policy.
   Kept separate from FIFO.v so policy definitions remain uncluttered. *)

(* Example: candidates = [j1; j2; j3], j1 not ready, j2 ready, j3 ready.
   choose_fifo returns j2 (first ready in order). *)
Section FIFOExample.

  (* Concrete jobs *)
  Let j1 : JobId := 0.
  Let j2 : JobId := 1.
  Let j3 : JobId := 2.

  (* job_map: all jobs have release=0, cost=1, deadline=10 *)
  Let jobs : JobId -> Job := fun _ =>
    mkJob 0 0 0 1 10.

  (* A schedule where j2 and j3 are ready but j1 is already completed:
     j1 has service >= cost (completed), so not eligible, hence not ready.
     We model this by a schedule that ran j1 at t=0: sched 0 0 = Some j1. *)
  Let sched : Schedule := fun t c =>
    if (t =? 0) && (c =? 0) then Some j1 else None.

  (* At t=1, j1 is completed (service_job 1 sched j1 1 = 1 >= cost 1).
     j2 and j3 have service 0 < cost 1, are released (release=0 <= 1),
     and not running (sched 1 _ = None for all c).
     Hence j2 and j3 are ready at t=1. *)

  Example choose_fifo_example :
      choose_fifo jobs 1 sched 1 [j1; j2; j3] = Some j2.
  Proof.
    unfold choose_fifo, readyb, j1, j2, j3, jobs, sched.
    simpl.
    reflexivity.
  Qed.

End FIFOExample.
