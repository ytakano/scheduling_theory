From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Import ListNotations.

(** Infrastructure for the future infinite offset-aware window-DBF cutoff.
    This file intentionally stops at arithmetic periodicity facts; the full
    window-DBF cutoff theorem is a later proof layer. *)

Fixpoint periodic_max_offset
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      Nat.max (offset τ) (periodic_max_offset offset enumT')
  end.

Definition offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  let horizon_base :=
      periodic_max_offset offset enumT +
      periodic_max_relative_deadline tasks enumT in
  horizon_base + S horizon_base * periodic_hyperperiod tasks enumT.

Lemma periodic_max_offset_ge :
  forall offset enumT τ,
    In τ enumT ->
    offset τ <= periodic_max_offset offset enumT.
Proof.
  intros offset enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma hyperperiod_as_task_period_multiple :
  forall tasks enumT τ,
    In τ enumT ->
    exists q,
      periodic_hyperperiod tasks enumT =
      q * task_period (tasks τ).
Proof.
  intros tasks enumT τ Hin.
  destruct (periodic_hyperperiod_divides tasks enumT τ Hin) as [q Hq].
  exists q.
  exact Hq.
Qed.

Lemma expected_release_shift_by_hyperperiod :
  forall tasks offset enumT τ k,
    In τ enumT ->
    exists q,
      forall n,
        expected_release tasks offset τ (k + n * q) =
        expected_release tasks offset τ k +
        n * periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset enumT τ k Hin.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  exists q.
  intros n.
  unfold expected_release.
  rewrite Hhp.
  lia.
Qed.

Lemma expected_deadline_shift_by_hyperperiod :
  forall tasks offset enumT τ k,
    In τ enumT ->
    exists q,
      forall n,
        expected_abs_deadline tasks offset τ (k + n * q) =
        expected_abs_deadline tasks offset τ k +
        n * periodic_hyperperiod tasks enumT.
Proof.
  intros tasks offset enumT τ k Hin.
  destruct (hyperperiod_as_task_period_multiple tasks enumT τ Hin) as [q Hhp].
  exists q.
  intros n.
  unfold expected_abs_deadline, expected_release.
  rewrite Hhp.
  lia.
Qed.
