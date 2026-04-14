From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.ResponseTimeSearch.

Definition rt_job0 : Job := mkJob 0 0 1 2 5.
Definition rt_job1 : Job := mkJob 0 1 4 1 8.

Definition rt_jobs (j : JobId) : Job :=
  match j with
  | 0 => rt_job0
  | _ => rt_job1
  end.

Definition rt_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    match t with
    | 0 => None
    | 1 => Some 0
    | 2 => Some 0
    | 3 => Some 1
    | 4 => Some 1
    | _ => None
    end
  else None.

Example rt_sched_busy_window_candidate :
  busy_window_candidate rt_sched 1 5.
Proof.
  apply busy_interval_with_boundaries_is_busy_window_candidate.
  - split.
    + lia.
    + intros t Ht.
      exists (if t <? 3 then 0 else 1).
      unfold rt_sched.
      rewrite Nat.eqb_refl.
      destruct t as [| [| [| [| [| t']]]]]; simpl in *; try reflexivity; lia.
  - unfold cpu_busy_at, rt_sched.
    right.
    unfold cpu_busy_at, rt_sched.
    rewrite Nat.eqb_refl.
    simpl.
    intro Hbusy.
    destruct Hbusy as [j Hj].
    discriminate.
  - unfold cpu_busy_at, rt_sched.
    rewrite Nat.eqb_refl.
    simpl.
    intro Hbusy.
    destruct Hbusy as [j Hj].
    discriminate.
Qed.

Example rt_response_time_candidate_ex :
  response_time_candidate rt_jobs 0 3.
Proof.
  unfold response_time_candidate, rt_jobs, rt_job0.
  simpl.
  lia.
Qed.

Example rt_response_time_search_reduction_ex :
  response_time_search_witness rt_jobs rt_sched 0 3 1 5.
Proof.
  apply response_time_search_reduction.
  - exact rt_response_time_candidate_ex.
  - exact rt_sched_busy_window_candidate.
  - simpl. lia.
  - simpl. lia.
Qed.
