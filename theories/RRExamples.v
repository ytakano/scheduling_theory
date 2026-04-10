(* Fully constructive: no Classical import. *)
From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.
Require Import UniPolicies.RoundRobin.
Import ListNotations.

(**
  RRExamples.v
  ============
  Concrete examples for the Round Robin dispatch policy.

  Design:
    Two jobs (ids 0 and 1) on a single CPU with unit quantum (q=1).
    The CandidateSource encodes the RR rotation: at t=0 the wheel is
    [0; 1]; at t=1 job 0 has run so it moves to the back: [1; 0];
    for t>=2 both jobs are completed and the order is irrelevant.

    This shows that rr_scheduler_on and rr_policy_scheduler_on are
    inhabited by a concrete schedule.
*)

(* ================================================================= *)
(** ** Shared definitions (module-level to avoid Section let-shadowing) *)
(* ================================================================= *)

(* All jobs: release=0, arrival=0, cost=1, deadline=4 *)
Definition rr_example_jobs (_ : JobId) : Job := mkJob 0 0 0 1 4.

(* Two-job set: jobs 0 and 1 *)
Definition J_rr (j : JobId) : Prop := j = 0 \/ j = 1.

(* Unit-quantum RR candidate source:
     t = 1: job 1 first (job 0 ran at t=0, rotated to back)
     otherwise: [0; 1] (initial order or both done) *)
Definition rr_example_cands : CandidateSource :=
  fun _jobs _m _sched t =>
    if t =? 1 then [1; 0] else [0; 1].

(* Witness schedule: job 0 at t=0, job 1 at t=1, idle thereafter *)
Definition rr_example_sched : Schedule := fun t c =>
  if c =? 0 then
    if t =? 0 then Some 0
    else if t =? 1 then Some 1
    else None
  else None.

(* ================================================================= *)
(** ** Basic computation examples                                      *)
(* ================================================================= *)

(* At t=0: job 0 eligible, job 1 eligible.
   RR queue = [0; 1] → choose_rr returns 0. *)
Example rr_step0 :
    choose_rr rr_example_jobs 1 rr_example_sched 0 [0; 1] = Some 0.
Proof. reflexivity. Qed.

(* At t=1: job 0 completed (ran at t=0), job 1 eligible.
   RR queue = [1; 0] → choose_rr returns 1. *)
Example rr_step1 :
    choose_rr rr_example_jobs 1 rr_example_sched 1 [1; 0] = Some 1.
Proof. reflexivity. Qed.

(* At t=2: both jobs completed; choose_rr returns None. *)
Example rr_step2 :
    choose_rr rr_example_jobs 1 rr_example_sched 2 [0; 1] = None.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** CandidateSourceSpec                                             *)
(* ================================================================= *)

Lemma rr_example_cands_spec : CandidateSourceSpec J_rr rr_example_cands.
Proof.
  refine (mkCandidateSourceSpec J_rr rr_example_cands _ _ _).
  - (* soundness: In j (rr_example_cands ...) → J_rr j *)
    intros _jobs _m _sched t j Hin.
    unfold rr_example_cands in Hin.
    destruct (t =? 1); simpl in Hin.
    + destruct Hin as [H | [H | []]].
      * right. exact (eq_sym H).
      * left.  exact (eq_sym H).
    + destruct Hin as [H | [H | []]].
      * left.  exact (eq_sym H).
      * right. exact (eq_sym H).
  - (* completeness: J_rr j → eligible j t → In j (rr_example_cands ...) *)
    intros _jobs _m _sched t j HJ _.
    unfold rr_example_cands.
    destruct (t =? 1); simpl.
    + destruct HJ as [-> | ->]; [right; left | left]; reflexivity.
    + destruct HJ as [-> | ->]; [left | right; left]; reflexivity.
  - (* prefix extensionality: rr_example_cands ignores sched *)
    intros _jobs _m s1 s2 t _.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** Service helpers                                                 *)
(* ================================================================= *)

(* Helper: job 0 never runs after t=0 *)
Lemma rr_example_cpu_count_j0_pos : forall t,
    cpu_count 1 rr_example_sched 0 (S t) = 0.
Proof.
  intro t.
  unfold cpu_count, runs_on, rr_example_sched.
  simpl.
  (* After simpl: S t =? 0 = false, reduces to (t =? 0 ? Some 1 : None) *)
  destruct (t =? 0); reflexivity.
Qed.

(* Helper: job 1 never runs after t=1 *)
Lemma rr_example_cpu_count_j1_pos2 : forall t,
    cpu_count 1 rr_example_sched 1 (S (S t)) = 0.
Proof.
  intro t.
  unfold cpu_count, runs_on, rr_example_sched.
  simpl.
  (* After simpl: S(S t) =? 0 = false, S(S t) =? 1 = false for S t =? 0 = false *)
  destruct (t =? 0); reflexivity.
Qed.

Lemma rr_example_service_j0 : forall t,
    1 <= t -> service_job 1 rr_example_sched 0 t = 1.
Proof.
  intros t Hle.
  induction t as [| t' IH].
  - lia.
  - destruct t' as [| t''].
    + (* t = 1: direct computation *)
      reflexivity.
    + (* t = S(S t''), use IH *)
      rewrite service_job_step.
      rewrite (rr_example_cpu_count_j0_pos t'').
      rewrite Nat.add_0_r.
      apply IH. lia.
Qed.

Lemma rr_example_service_j1 : forall t,
    2 <= t -> service_job 1 rr_example_sched 1 t = 1.
Proof.
  intros t Hle.
  induction t as [| t' IH].
  - lia.
  - destruct t' as [| t''].
    + lia.
    + destruct t'' as [| t'''].
      * (* t = 2: direct computation *)
        reflexivity.
      * (* t = S(S(S t''')), use IH *)
        rewrite service_job_step.
        rewrite (rr_example_cpu_count_j1_pos2 t''').
        rewrite Nat.add_0_r.
        apply IH. lia.
Qed.

(* ================================================================= *)
(** ** scheduler_rel witness                                           *)
(* ================================================================= *)

Lemma rr_example_satisfies_scheduler :
    scheduler_rel
      (rr_scheduler_on J_rr rr_example_cands rr_example_cands_spec)
      rr_example_jobs 1 rr_example_sched.
Proof.
  unfold rr_scheduler_on, rr_bundle, uni_scheduler_on.
  unfold single_cpu_algorithm_scheduler_on, single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intro t.
    split.
    + (* rr_example_sched t 0 = choose_rr ... t (rr_example_cands ...) *)
      destruct t as [| [| t'']].
      * (* t = 0 *)
        unfold rr_example_cands, rr_example_sched, choose_rr. reflexivity.
      * (* t = 1 *)
        unfold rr_example_cands, rr_example_sched, choose_rr. reflexivity.
      * (* t = S(S t''): both jobs completed, both sides = None *)
        assert (H0 : eligibleb rr_example_jobs 1 rr_example_sched 0 (S (S t'')) = false).
        { unfold eligibleb, rr_example_jobs.
          rewrite (rr_example_service_j0 (S (S t'')) ltac:(lia)). reflexivity. }
        assert (H1 : eligibleb rr_example_jobs 1 rr_example_sched 1 (S (S t'')) = false).
        { unfold eligibleb, rr_example_jobs.
          rewrite (rr_example_service_j1 (S (S t'')) ltac:(lia)). reflexivity. }
        assert (HNone : choose_rr rr_example_jobs 1 rr_example_sched (S (S t''))
                          (rr_example_cands rr_example_jobs 1 rr_example_sched (S (S t''))) = None).
        { unfold rr_example_cands. simpl.
          unfold choose_rr. rewrite H0. rewrite H1. reflexivity. }
        rewrite HNone.
        unfold rr_example_sched.
        reflexivity.
    + (* forall c, 0 < c → rr_example_sched t c = None *)
      intros c Hc.
      unfold rr_example_sched.
      destruct c as [| c']. lia. reflexivity.
Qed.

(* ================================================================= *)
(** ** Feasibility and validity                                        *)
(* ================================================================= *)

Lemma rr_example_feasible :
    feasible_schedule_on J_rr rr_example_jobs 1 rr_example_sched.
Proof.
  intros j HJ Hmiss.
  apply Hmiss.
  destruct HJ as [-> | ->]; unfold completed, rr_example_jobs.
  - change (1 <= service_job 1 rr_example_sched 0 4).
    rewrite (rr_example_service_j0 4 ltac:(lia)). lia.
  - change (1 <= service_job 1 rr_example_sched 1 4).
    rewrite (rr_example_service_j1 4 ltac:(lia)). lia.
Qed.

Lemma rr_example_valid :
    valid_schedule rr_example_jobs 1 rr_example_sched.
Proof.
  exact (single_cpu_algorithm_valid rr_generic_spec rr_example_cands
           rr_example_jobs rr_example_sched
           rr_example_satisfies_scheduler).
Qed.

(* ================================================================= *)
(** ** schedulable_by_on                                               *)
(* ================================================================= *)

Theorem rr_two_jobs_schedulable :
    schedulable_by_on J_rr
      (rr_scheduler_on J_rr rr_example_cands rr_example_cands_spec)
      rr_example_jobs 1.
Proof.
  exists rr_example_sched.
  split. exact rr_example_satisfies_scheduler.
  split. exact rr_example_valid.
  exact rr_example_feasible.
Qed.
