From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Sporadic.SporadicTasks.

(* ===== Finite Horizon Jobset for Sporadic Tasks ===== *)

(* The sporadic finite-horizon jobset up to horizon H:
   all jobs j such that
   - their task is in scope (T)
   - they satisfy the sporadic generation predicate (generated_by_sporadic_task)
   - their release time is strictly before H

   Unlike periodic_jobset_upto, releases are constrained by a lower bound only.
   The minimum inter-arrival constraint is tracked separately in sporadic_job_model_on. *)
Definition sporadic_jobset_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> Prop :=
  fun j =>
    T (job_task (jobs j)) /\
    generated_by_sporadic_task tasks jobs j /\
    job_release (jobs j) < H.

(* Boolean version for use with CandidateSourceSpec / enum_candidates_spec. *)
Definition sporadic_jobset_upto_bool
    (T_bool : TaskId -> bool)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time) : JobId -> bool :=
  fun j =>
    T_bool (job_task (jobs j))
    && generated_by_sporadic_task_b tasks jobs j
    && Nat.ltb (job_release (jobs j)) H.

Lemma sporadic_jobset_upto_bool_spec :
  forall T T_bool tasks jobs H,
    (forall τ, T_bool τ = true <-> T τ) ->
    forall j,
      sporadic_jobset_upto_bool T_bool tasks jobs H j = true <->
      sporadic_jobset_upto T tasks jobs H j.
Proof.
  intros T T_bool tasks jobs H HT j.
  unfold sporadic_jobset_upto_bool, sporadic_jobset_upto.
  rewrite !andb_true_iff, generated_by_sporadic_task_b_spec, Nat.ltb_lt, HT.
  tauto.
Qed.

Lemma sporadic_jobset_upto_implies_task_in_scope :
  forall T tasks jobs H j,
    sporadic_jobset_upto T tasks jobs H j ->
    T (job_task (jobs j)).
Proof.
  intros T tasks jobs H j [HT _].
  exact HT.
Qed.

Lemma sporadic_jobset_upto_implies_generated :
  forall T tasks jobs H j,
    sporadic_jobset_upto T tasks jobs H j ->
    generated_by_sporadic_task tasks jobs j.
Proof.
  intros T tasks jobs H j [_ [Hgen _]]. exact Hgen.
Qed.

Lemma sporadic_jobset_upto_implies_valid_job_of_task :
  forall T tasks jobs H j,
    sporadic_jobset_upto T tasks jobs H j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros T tasks jobs H j Hjobset.
  exact (generated_sporadic_implies_valid_job_of_task tasks jobs j
    (sporadic_jobset_upto_implies_generated T tasks jobs H j Hjobset)).
Qed.

Lemma sporadic_jobset_upto_implies_release_lt :
  forall T tasks jobs H j,
    sporadic_jobset_upto T tasks jobs H j ->
    job_release (jobs j) < H.
Proof.
  intros T tasks jobs H j [_ [_ Hrel]].
  exact Hrel.
Qed.
