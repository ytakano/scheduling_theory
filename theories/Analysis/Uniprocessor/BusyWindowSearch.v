From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.

(* A busy-window candidate is a maximal busy interval on the single CPU. *)
Definition busy_window_candidate
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  maximal_busy_interval_from sched t1 t2.

(* A search witness covers the distinguished time point t. *)
Definition busy_window_witness
    (sched : Schedule) (t : Time) (t1 t2 : Time) : Prop :=
  busy_window_candidate sched t1 t2 /\
  t1 <= t /\ t <= t2.

Lemma busy_window_candidate_is_maximal_busy_interval :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    maximal_busy_interval_from sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  exact Hcand.
Qed.

Lemma maximal_busy_interval_is_busy_window_candidate :
  forall sched t1 t2,
    maximal_busy_interval_from sched t1 t2 ->
    busy_window_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hmax.
  exact Hmax.
Qed.

Lemma busy_window_candidate_decompose :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    busy_interval sched t1 t2 /\
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) /\
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 Hcand.
  apply maximal_busy_interval_from_decompose.
  exact Hcand.
Qed.

Lemma busy_window_candidate_busy_interval :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    busy_interval sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  exact (proj1 (busy_window_candidate_decompose sched t1 t2 Hcand)).
Qed.

Lemma busy_window_candidate_left_boundary :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    t1 = 0 \/ ~ cpu_busy_at sched (pred t1).
Proof.
  intros sched t1 t2 Hcand.
  exact (proj1 (proj2 (busy_window_candidate_decompose sched t1 t2 Hcand))).
Qed.

Lemma busy_window_candidate_right_boundary :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 Hcand.
  exact (proj2 (proj2 (busy_window_candidate_decompose sched t1 t2 Hcand))).
Qed.

Lemma busy_interval_with_boundaries_is_busy_window_candidate :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) ->
    ~ cpu_busy_at sched t2 ->
    busy_window_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hbusy Hleft Hright.
  unfold busy_window_candidate, maximal_busy_interval_from.
  split; [exact Hbusy |].
  split; assumption.
Qed.

Lemma busy_window_candidate_covers_time :
  forall sched t t1 t2,
    busy_window_witness sched t t1 t2 ->
    t1 <= t /\ t <= t2.
Proof.
  intros sched t t1 t2 [_ Hcover].
  exact Hcover.
Qed.

Lemma busy_window_candidate_covers_deadline :
  forall (jobs : JobId -> Job) sched j t1 t2,
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_abs_deadline (jobs j) /\
    job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs sched j t1 t2 Hwit.
  exact (busy_window_candidate_covers_time sched (job_abs_deadline (jobs j)) t1 t2 Hwit).
Qed.

Lemma busy_window_witness_from_candidate :
  forall sched t t1 t2,
    busy_window_candidate sched t1 t2 ->
    t1 <= t ->
    t <= t2 ->
    busy_window_witness sched t t1 t2.
Proof.
  intros sched t t1 t2 Hcand Hleft Hright.
  split; [exact Hcand | lia].
Qed.

Lemma busy_window_witness_monotone :
  forall sched t t1 t2 t1' t2',
    busy_window_witness sched t t1 t2 ->
    t1' <= t1 ->
    t2 <= t2' ->
    busy_window_candidate sched t1 t2 ->
    t1' <= t /\ t <= t2'.
Proof.
  intros sched t t1 t2 t1' t2' Hwit Hleft Hright _.
  destruct Hwit as [_ [Hge Hle]].
  lia.
Qed.

Lemma deadline_miss_inside_busy_window_candidate :
  forall (jobs : JobId -> Job) sched j t1 t2,
    missed_deadline jobs 1 sched j ->
    busy_window_candidate sched t1 t2 ->
    t1 <= job_abs_deadline (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j t1 t2 _ Hcand Hleft Hright.
  apply busy_window_witness_from_candidate; assumption.
Qed.

Lemma busy_window_candidate_cpu_supply_eq_length :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    cpu_service_between sched t1 t2 = t2 - t1.
Proof.
  intros sched t1 t2 Hcand.
  apply cpu_service_between_busy_interval_eq_length.
  apply busy_window_candidate_busy_interval.
  exact Hcand.
Qed.
