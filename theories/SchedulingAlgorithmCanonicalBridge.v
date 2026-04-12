From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Import ListNotations.

(* Generic canonical schedule predicates for a scheduling algorithm. *)

Definition matches_choose_at_with
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  sched t 0 = choose alg jobs 1 sched t (candidates_of jobs 1 sched t).

Definition matches_choose_before
    (alg : GenericSchedulingAlgorithm)
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    matches_choose_at_with alg jobs candidates_of sched t.

(* Finite horizon: one past the maximum absolute deadline in enumJ. *)
Definition deadline_horizon
    (jobs : JobId -> Job)
    (enumJ : list JobId) : nat :=
  S (fold_right Nat.max 0 (map (fun j => job_abs_deadline (jobs j)) enumJ)).

Lemma fold_right_max_upper_bound :
  forall (l : list nat) (x : nat),
    In x l ->
    x <= fold_right Nat.max 0 l.
Proof.
  intros l x Hin.
  induction l as [|h rest IH].
  - contradiction.
  - simpl.
    destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 rest).
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

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

Lemma J_implies_deadline_le_horizon :
  forall J enumJ jobs j,
    (forall j, J j -> In j enumJ) ->
    J j ->
    job_abs_deadline (jobs j) <= deadline_horizon jobs enumJ.
Proof.
  intros J enumJ jobs j Hcomplete HJj.
  pose proof (J_implies_deadline_lt_horizon J enumJ jobs j Hcomplete HJj) as Hlt.
  lia.
Qed.

Lemma J_jobs_complete_at_or_after_deadline :
  forall J jobs sched j t,
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    job_abs_deadline (jobs j) <= t ->
    completed jobs 1 sched j t.
Proof.
  intros J jobs sched j t _Hvalid Hfeas HJj Hdt.
  unfold completed.
  assert (Hnmiss : ~ missed_deadline jobs 1 sched j) by exact (Hfeas j HJj).
  unfold missed_deadline in Hnmiss.
  unfold completed in Hnmiss.
  assert (Hmono : service_job 1 sched j (job_abs_deadline (jobs j)) <=
                  service_job 1 sched j t)
    by (apply service_job_monotone; exact Hdt).
  lia.
Qed.

Lemma J_jobs_not_eligible_at_horizon :
  forall J enumJ jobs sched j t,
    (forall x, J x -> In x enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    deadline_horizon jobs enumJ <= t ->
    ~ eligible jobs 1 sched j t.
Proof.
  intros J enumJ jobs sched j t HJ_in Hvalid Hfeas HJj Hdt Helig.
  assert (Hdl : job_abs_deadline (jobs j) < deadline_horizon jobs enumJ).
  { exact (J_implies_deadline_lt_horizon J enumJ jobs j HJ_in HJj). }
  assert (Hcomp : completed jobs 1 sched j t).
  { apply (J_jobs_complete_at_or_after_deadline J jobs sched j t Hvalid Hfeas HJj). lia. }
  exact (proj2 Helig Hcomp).
Qed.

Lemma canonical_and_idle_implies_scheduler_rel_generic :
  forall alg J enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_choose_before alg jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (single_cpu_algorithm_schedule alg candidates_of) jobs 1 sched.
Proof.
  intros alg J enumJ candidates_of cand_spec jobs sched
         HJ_in Hvalid Hfeas Honly Hcanon Hidle.
  unfold single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + destruct (lt_dec t (deadline_horizon jobs enumJ)) as [Hlt | Hge].
      * exact (Hcanon t Hlt).
      * assert (Ht_H : deadline_horizon jobs enumJ <= t) by lia.
        rewrite (Hidle t Ht_H).
        symmetry.
        apply choose_none_if_no_eligible_candidate.
        intros j Hin Helig.
        destruct cand_spec as [Hsound _ _].
        assert (HJj : J j) by (exact (Hsound jobs 1 sched t j Hin)).
        exact (J_jobs_not_eligible_at_horizon J enumJ jobs sched j t
                 HJ_in Hvalid Hfeas HJj Ht_H Helig).
    + exact (Honly t).
Qed.
