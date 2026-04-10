From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import UniPolicies.EDF.
Import ListNotations.

(* ===== Phase 1: 有限 horizon を job 集合から作る ===== *)

(* The finite time horizon: one past the maximum absolute deadline in enumJ.
   Any job in enumJ has deadline strictly less than this value. *)
Definition deadline_horizon
    (jobs : JobId -> Job)
    (enumJ : list JobId) : nat :=
  S (fold_right Nat.max 0 (map (fun j => job_abs_deadline (jobs j)) enumJ)).

(* Helper: every element of a list is <= fold_right Nat.max 0 of that list. *)
Lemma fold_right_max_upper_bound :
  forall (l : list nat) (x : nat),
    In x l ->
    x <= fold_right Nat.max 0 l.
Proof.
  intros l x Hin.
  induction l as [| h rest IH].
  - contradiction.
  - simpl. destruct Hin as [-> | Hin'].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 rest).
      * apply IH. exact Hin'.
      * apply Nat.le_max_r.
Qed.

(* Any job in enumJ has deadline strictly less than deadline_horizon. *)
Lemma in_enum_implies_deadline_lt_horizon :
  forall jobs enumJ j,
    In j enumJ ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros jobs enumJ j Hin.
  unfold deadline_horizon.
  apply Nat.lt_succ_r.
  apply fold_right_max_upper_bound.
  exact (in_map (fun j0 => job_abs_deadline (jobs j0)) enumJ j Hin).
Qed.

(* Any job in J has deadline strictly less than deadline_horizon,
   provided enumJ is a complete enumeration of J. *)
Lemma J_implies_deadline_lt_horizon :
  forall J enumJ jobs j,
    (forall j, J j -> In j enumJ) ->
    J j ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros J enumJ jobs j Hcomplete HJj.
  apply in_enum_implies_deadline_lt_horizon.
  apply Hcomplete. exact HJj.
Qed.
