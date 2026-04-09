From Stdlib Require Import Arith Arith.PeanoNat Lia Bool List.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Import ListNotations.

(* Bridge between GenericDispatchSpec and the Scheduler abstraction.

   single_cpu_dispatch_schedule wraps a dispatch policy into a Scheduler
   relation for the single-CPU (m = 1) case.  The relation holds for a
   schedule sched when:
     - CPU 0 follows the dispatch policy at every time step
     - All other CPUs are idle                                            *)

Definition single_cpu_dispatch_schedule
    (spec : GenericDispatchSpec)
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    forall t,
      sched t 0 = spec.(dispatch) jobs m sched t (candidates_of jobs m sched t) /\
      forall c, 0 < c -> sched t c = None).

(* A schedule produced by single_cpu_dispatch_schedule is valid
   (on 1 CPU), because dispatch_eligible guarantees every dispatched job
   is eligible, and idle CPUs carry no job. *)
Lemma single_cpu_dispatch_valid :
    forall spec candidates_of jobs sched,
      scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 sched ->
      valid_schedule jobs 1 sched.
Proof.
  intros spec cands jobs sched Hrel.
  unfold valid_schedule.
  intros j t c Hc Hsched.
  (* c < 1 means c = 0 *)
  assert (c = 0) by lia. subst c.
  (* sched t 0 = dispatch ... *)
  destruct (Hrel t) as [Heq _].
  rewrite Heq in Hsched.
  (* dispatch returned Some j, so j is eligible *)
  exact (spec.(dispatch_eligible) jobs 1 sched t _ j Hsched).
Qed.

(* ===== Candidate Source Abstraction ===== *)

(* CandidateSource: a function that supplies the candidate job list at each time step. *)
Definition CandidateSource :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId.

(* CandidateSourceSpec: contract that a candidate source must satisfy with respect to
   a job set J.
   - candidates_sound: every candidate belongs to J
   - candidates_complete: every eligible job in J is in the candidate list
   - candidates_prefix_extensional: the candidate list depends only on the
     schedule history strictly before time t (prevents circular reasoning) *)
Record CandidateSourceSpec
    (J : JobId -> Prop)
    (candidates_of : CandidateSource) : Prop := mkCandidateSourceSpec {
  candidates_sound :
    forall jobs m sched t j,
      In j (candidates_of jobs m sched t) -> J j;
  candidates_complete :
    forall jobs m sched t j,
      J j -> eligible jobs m sched j t ->
      In j (candidates_of jobs m sched t);
  candidates_prefix_extensional :
    forall jobs m s1 s2 t,
      (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
      candidates_of jobs m s1 t = candidates_of jobs m s2 t
}.
