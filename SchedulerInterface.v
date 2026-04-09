From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
Require Import Base.
Require Import ScheduleModel.

(* Abstract scheduler: maps a job set and CPU count to a schedule. *)
Parameter Scheduler : Type.
Parameter run_scheduler : Scheduler -> (JobId -> Job) -> nat -> Schedule.

(* A job set is schedulable by algorithm alg if the produced schedule
   is valid and feasible. *)
Definition schedulable_by
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  valid_schedule jobs m (run_scheduler alg jobs m) /\
  feasible_schedule jobs m (run_scheduler alg jobs m).

(* Subset variant: schedulable by alg restricted to job set J. *)
Definition schedulable_by_on (J : JobId -> Prop)
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  valid_schedule jobs m (run_scheduler alg jobs m) /\
  feasible_schedule_on J jobs m (run_scheduler alg jobs m).

(* --- Lv.0-5: schedulable_by / schedulable_by_on --- *)

(* schedulable_by implies feasible: the produced schedule witnesses existence. *)
Lemma schedulable_by_implies_feasible :
    forall alg jobs m,
      schedulable_by alg jobs m -> feasible jobs m.
Proof.
  intros alg jobs m [Hvalid Hfeas].
  unfold feasible.
  exists (run_scheduler alg jobs m).
  split; assumption.
Qed.

(* schedulable_by implies schedulable_by_on for any job subset J. *)
Lemma schedulable_by_implies_schedulable_by_on :
    forall (J : JobId -> Prop) alg jobs m,
      schedulable_by alg jobs m -> schedulable_by_on J alg jobs m.
Proof.
  intros J alg jobs m [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j _HJ. exact (Hfeas j).
Qed.

(* schedulable_by_on is monotone: narrowing the job set preserves schedulability. *)
Lemma schedulable_by_on_monotone :
    forall (J J' : JobId -> Prop) alg jobs m,
      (forall j, J j -> J' j) ->
      schedulable_by_on J' alg jobs m ->
      schedulable_by_on J alg jobs m.
Proof.
  intros J J' alg jobs m Hsubset [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j HJ. exact (Hfeas j (Hsubset j HJ)).
Qed.
