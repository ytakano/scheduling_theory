From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicOffsetWindowCutoff.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicConcreteAnalysis.

Import ListNotations.

(** * Conservative bounded cutoff surface for jittered-periodic window DBF

    The bound extends the existing offset-window cutoff by the maximum release
    jitter.  This batch proves soundness for windows bounded by the cutoff; the
    later hyperperiod-shift theorem will lift this to all windows. *)

Fixpoint jittered_max_release_jitter
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      Nat.max (jitter τ) (jittered_max_release_jitter jitter enumT')
  end.

Definition jittered_offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : Time :=
  offset_window_dbf_cutoff_bound tasks offset enumT +
  jittered_max_release_jitter jitter enumT.

Definition jittered_offset_window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId) : bool :=
  jittered_window_dbf_test_upto
    tasks offset jitter enumT
    (jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT).

Lemma jittered_max_release_jitter_ge :
  forall jitter enumT τ,
    In τ enumT ->
    jitter τ <= jittered_max_release_jitter jitter enumT.
Proof.
  intros jitter enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Theorem jittered_offset_window_dbf_test_by_cutoff_bounded_sound :
  forall tasks offset jitter enumT t1 t2,
    jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT = true ->
    t1 <= t2 ->
    t2 <= jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT t1 t2 Htest Hle12 Hle2.
  unfold jittered_offset_window_dbf_test_by_cutoff in Htest.
  eapply jittered_window_dbf_test_upto_true_implies_bounded_window_dbf; eauto.
Qed.
