From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicWindowDemandBound.

Import ListNotations.

(** * Bounded concrete checks for jittered-periodic window DBF

    This file reuses the periodic critical-window enumeration as a bounded
    checker surface.  It proves only bounded-window soundness; hyperperiod
    transport for an infinite cutoff is kept in the offset-cutoff layer. *)

Definition jittered_window_dbf_test_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun w =>
       let '(t1, t2) := w in
       taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2
       <=? t2 - t1)
    (critical_dbf_windows_upto tasks offset enumT H).

Definition first_jittered_window_dbf_overload_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : option (Time * Time) :=
  find
    (fun w =>
       let '(t1, t2) := w in
       negb
         (taskset_jittered_periodic_dbf_window
            tasks offset jitter enumT t1 t2 <=? t2 - t1))
    (critical_dbf_windows_upto tasks offset enumT H).

Lemma first_jittered_window_dbf_overload_upto_some :
  forall tasks offset jitter enumT H t1 t2,
    first_jittered_window_dbf_overload_upto
      tasks offset jitter enumT H = Some (t1, t2) ->
    t2 - t1 <
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2.
Proof.
  intros tasks offset jitter enumT H t1 t2 Hfind.
  unfold first_jittered_window_dbf_overload_upto in Hfind.
  apply find_some in Hfind.
  destruct Hfind as [_ Hover].
  apply negb_true_iff in Hover.
  apply Nat.leb_gt in Hover.
  exact Hover.
Qed.

Lemma jittered_critical_dbf_windows_upto_sound :
  forall tasks offset jitter enumT H t1 t2,
    jittered_window_dbf_test_upto tasks offset jitter enumT H = true ->
    In (t1, t2) (critical_dbf_windows_upto tasks offset enumT H) ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT H t1 t2 Htest Hin.
  unfold jittered_window_dbf_test_upto in Htest.
  apply forallb_forall with (x := (t1, t2)) in Htest; auto.
  now apply Nat.leb_le in Htest.
Qed.

Theorem jittered_window_dbf_test_upto_true_implies_bounded_window_dbf :
  forall tasks offset jitter enumT H t1 t2,
    jittered_window_dbf_test_upto tasks offset jitter enumT H = true ->
    t1 <= t2 ->
    t2 <= H ->
    taskset_jittered_periodic_dbf_window
      tasks offset jitter enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset jitter enumT H t1 t2 Htest Hle12 Hle2H.
  eapply jittered_critical_dbf_windows_upto_sound; eauto.
  apply critical_dbf_windows_upto_complete; assumption.
Qed.
