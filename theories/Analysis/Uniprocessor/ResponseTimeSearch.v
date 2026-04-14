From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.

(* A response-time candidate is any bound within the job's release-to-deadline span. *)
Definition response_time_candidate
    (jobs : JobId -> Job) (j : JobId) (R : Time) : Prop :=
  job_release (jobs j) + R <= job_abs_deadline (jobs j).

(* Search-space reduction is expressed as a busy-window candidate that covers the deadline. *)
Definition response_time_search_witness
    (jobs : JobId -> Job) (sched : Schedule) (j : JobId)
    (R t1 t2 : Time) : Prop :=
  response_time_candidate jobs j R /\
  busy_window_candidate sched t1 t2 /\
  t1 <= job_release (jobs j) /\
  job_abs_deadline (jobs j) <= t2.

(* Finite-horizon response-time search only needs a covering busy prefix. *)
Definition response_time_search_prefix_witness
    (jobs : JobId -> Job) (sched : Schedule) (j : JobId)
    (R t1 t2 : Time) : Prop :=
  response_time_candidate jobs j R /\
  busy_prefix_candidate sched t1 t2 /\
  t1 <= job_release (jobs j) /\
  job_abs_deadline (jobs j) <= t2.

Lemma response_time_candidate_within_job_horizon :
  forall jobs j R,
    response_time_candidate jobs j R ->
    job_release (jobs j) + R <= job_abs_deadline (jobs j).
Proof.
  intros jobs j R Hcand.
  exact Hcand.
Qed.

Lemma response_time_search_reduction :
  forall jobs sched j R t1 t2,
    response_time_candidate jobs j R ->
    busy_window_candidate sched t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    response_time_search_witness jobs sched j R t1 t2.
Proof.
  intros jobs sched j R t1 t2 Hcand Hbusy Hrel Hdl.
  split; [exact Hcand |].
  split; [exact Hbusy |].
  split; assumption.
Qed.

Lemma response_time_search_prefix_reduction :
  forall jobs sched j R t1 t2,
    response_time_candidate jobs j R ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= job_release (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    response_time_search_prefix_witness jobs sched j R t1 t2.
Proof.
  intros jobs sched j R t1 t2 Hcand Hbusy Hrel Hdl.
  split; [exact Hcand |].
  split; [exact Hbusy |].
  split; assumption.
Qed.

Lemma response_time_search_witness_has_busy_window :
  forall jobs sched j R t1 t2,
    response_time_search_witness jobs sched j R t1 t2 ->
    busy_window_candidate sched t1 t2.
Proof.
  intros jobs sched j R t1 t2 [_ [Hbusy _]].
  exact Hbusy.
Qed.

Lemma response_time_search_prefix_witness_has_busy_prefix :
  forall jobs sched j R t1 t2,
    response_time_search_prefix_witness jobs sched j R t1 t2 ->
    busy_prefix_candidate sched t1 t2.
Proof.
  intros jobs sched j R t1 t2 [_ [Hbusy _]].
  exact Hbusy.
Qed.

Lemma response_time_search_witness_covers_deadline :
  forall jobs sched j R t1 t2,
    response_time_search_witness jobs sched j R t1 t2 ->
    t1 <= job_abs_deadline (jobs j) /\ job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs sched j R t1 t2 [Hcand [_ [Hrel Hdl]]].
  split.
  - pose proof (response_time_candidate_within_job_horizon jobs j R Hcand) as Hspan.
    lia.
  - exact Hdl.
Qed.

Lemma response_time_search_prefix_witness_covers_deadline :
  forall jobs sched j R t1 t2,
    response_time_search_prefix_witness jobs sched j R t1 t2 ->
    t1 <= job_abs_deadline (jobs j) /\ job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs sched j R t1 t2 [Hcand [_ [Hrel Hdl]]].
  split.
  - pose proof (response_time_candidate_within_job_horizon jobs j R Hcand) as Hspan.
    lia.
  - exact Hdl.
Qed.

Lemma response_time_search_witness_implies_prefix :
  forall jobs sched j R t1 t2,
    response_time_search_witness jobs sched j R t1 t2 ->
    response_time_search_prefix_witness jobs sched j R t1 t2.
Proof.
  intros jobs sched j R t1 t2 [Hcand [Hbusy [Hrel Hdl]]].
  split; [exact Hcand |].
  split.
  - exact (busy_window_candidate_is_busy_prefix_candidate sched t1 t2 Hbusy).
  - split; assumption.
Qed.

Lemma missed_deadline_with_response_time_search_witness :
  forall jobs sched j R t1 t2,
    missed_deadline jobs 1 sched j ->
    response_time_search_witness jobs sched j R t1 t2 ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j R t1 t2 Hmiss [Hcand [Hbusy [Hrel Hdl]]].
  pose proof (response_time_candidate_within_job_horizon jobs j R Hcand) as Hspan.
  apply deadline_miss_inside_busy_window_candidate; try assumption.
  lia.
Qed.

Lemma missed_deadline_with_response_time_search_prefix_witness :
  forall jobs sched j R t1 t2,
    missed_deadline jobs 1 sched j ->
    response_time_search_prefix_witness jobs sched j R t1 t2 ->
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j R t1 t2 Hmiss [Hcand [Hbusy [Hrel Hdl]]].
  pose proof (response_time_candidate_within_job_horizon jobs j R Hcand) as Hspan.
  apply deadline_miss_inside_busy_prefix_candidate; try assumption.
  lia.
Qed.
