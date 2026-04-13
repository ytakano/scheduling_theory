From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.

(* Abstract scheduler: a relation between a job set, CPU count, and schedule.
   scheduler_rel alg jobs m sched holds when sched is a valid execution of alg. *)
Record Scheduler : Type := mkScheduler {
  scheduler_rel : (JobId -> Job) -> nat -> Schedule -> Prop
}.

(* A job set is schedulable by algorithm alg if there exists a schedule
   that the algorithm produces and that is both valid and feasible. *)
Definition schedulable_by
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched,
    scheduler_rel alg jobs m sched /\
    valid_schedule jobs m sched /\
    feasible_schedule jobs m sched.

(* Subset variant: schedulable by alg restricted to job set J. *)
Definition schedulable_by_on (J : JobId -> Prop)
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched,
    scheduler_rel alg jobs m sched /\
    valid_schedule jobs m sched /\
    feasible_schedule_on J jobs m sched.

(* --- Lv.0-5: schedulable_by / schedulable_by_on --- *)

(* schedulable_by implies feasible: the produced schedule witnesses existence. *)
Lemma schedulable_by_implies_feasible :
    forall alg jobs m,
      schedulable_by alg jobs m -> feasible jobs m.
Proof.
  intros alg jobs m [sched [_Hrel [Hvalid Hfeas]]].
  unfold feasible.
  exists sched.
  split; assumption.
Qed.

(* schedulable_by implies schedulable_by_on for any job subset J. *)
Lemma schedulable_by_implies_schedulable_by_on :
    forall (J : JobId -> Prop) alg jobs m,
      schedulable_by alg jobs m -> schedulable_by_on J alg jobs m.
Proof.
  intros J alg jobs m [sched [Hrel [Hvalid Hfeas]]].
  unfold schedulable_by_on, feasible_schedule_on.
  exists sched.
  split; [exact Hrel |].
  split; [exact Hvalid |].
  intros j _HJ. exact (Hfeas j).
Qed.

(* schedulable_by_on is monotone: narrowing the job set preserves schedulability. *)
Lemma schedulable_by_on_monotone :
    forall (J J' : JobId -> Prop) alg jobs m,
      (forall j, J j -> J' j) ->
      schedulable_by_on J' alg jobs m ->
      schedulable_by_on J alg jobs m.
Proof.
  intros J J' alg jobs m Hsubset [sched [Hrel [Hvalid Hfeas]]].
  unfold schedulable_by_on, feasible_schedule_on.
  exists sched.
  split; [exact Hrel |].
  split; [exact Hvalid |].
  intros j HJ. exact (Hfeas j (Hsubset j HJ)).
Qed.

(* Build schedulable_by_on directly from a witness schedule. *)
Lemma schedulable_by_on_intro :
    forall (J : JobId -> Prop) alg jobs m sched,
      scheduler_rel alg jobs m sched ->
      valid_schedule jobs m sched ->
      feasible_schedule_on J jobs m sched ->
      schedulable_by_on J alg jobs m.
Proof.
  intros J alg jobs m sched Hrel Hvalid Hfeas.
  unfold schedulable_by_on.
  exists sched.
  split; [exact Hrel |].
  split; assumption.
Qed.
