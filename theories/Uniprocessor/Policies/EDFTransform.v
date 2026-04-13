From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleTransform.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.SchedulingAlgorithmCanonicalBridge.
From RocqSched Require Import Uniprocessor.Policies.Common.MetricChooserLemmas.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
Import ListNotations.

(* ===== Phase 1: finite horizon helpers are shared in SchedulingAlgorithmCanonicalBridge ===== *)

(* ===== Phase 2: repair 対象の 2 時刻を固定する ===== *)

(* 4. first_violation_has_repair_witness:
   EDF violation at (t, j) を witness にして、swap の 2 時刻 (t, t') と
   交換対象 job j' を取り出す。
   完全 Constructive: le_lt_dec / lt_dec のみ使用。Classical 不要。 *)
Lemma first_violation_has_repair_witness :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched (H : nat) t j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t < H ->
    sched t 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j' t',
      J j' /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      t <= t' /\
      t' < job_abs_deadline (jobs j') /\
      sched t' 0 = Some j'.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H t j
         _HJbool Hvalid Hfeas _HtH Hsched Hviol.
  (* Step 1: unfold violation to get running job j0 and earlier-deadline job j' *)
  unfold edf_violation_at_with, edf_violation_at_in in Hviol.
  destruct Hviol as [j0 [j' [_HJj0 [HJj' [Hsched0 [_Hin [Helig Hlt]]]]]]].
  (* Step 2: j0 = j from deterministic schedule *)
  rewrite Hsched in Hsched0.
  injection Hsched0 as Heq. subst j0.
  (* Step 3: j' is eligible and J j', so it runs before its deadline *)
  destruct (eligible_feasible_implies_runs_later_before_deadline
              J jobs sched j' t HJj' Hvalid Hfeas Helig)
      as [t' [Hle [Hlt' Hrun]]].
  (* Assemble witness (j', t') *)
  exists j', t'.
  split. exact HJj'.
  split. exact Helig.
  split. exact Hlt.
  split. exact Hle.
  split. exact Hlt'.
  exact Hrun.
Qed.

(* ===== Phase 7: 最初の violation を 1 つ潰す ===== *)

(* 18'. first_violation_yields_canonical_repair_job:
   From an EDF violation at t (running job j in J), extract the canonical
   choose_edf winner j' such that:
   - j' is in the candidates list
   - j' is eligible at t
   - j' has STRICTLY earlier deadline than j (violation gives j_viol with strict <;
     choose_edf minimum has deadline <= j_viol, so still strictly < deadline(j))
   - j' <> j (different deadlines)
   - choose_edf returns j'
   Fully constructive: no Classical. *)
Lemma first_violation_yields_canonical_repair_job :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      j' <> j /\
      choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.
Proof.
  intros J candidates_of cand_spec jobs sched t j _Hvalid Hsched _HJj Hviol.
  (* Step 1: extract violation witness j_viol *)
  unfold edf_violation_at_with, edf_violation_at_in in Hviol.
  destruct Hviol as [j0 [j_viol [_HJj0 [_HJj_viol [Hsched0 [Hin_viol [Helig_viol Hlt_viol]]]]]]].
  rewrite Hsched in Hsched0. injection Hsched0 as Heq. subst j0.
  (* Step 2: choose_edf returns some j' (j_viol is eligible and in candidates) *)
  destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t))
      as [j' Hchoose].
  { exists j_viol. split. exact Hin_viol. exact Helig_viol. }
  (* Step 3: properties of j' *)
  assert (Hj'_elig : eligible jobs 1 sched j' t).
  { exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose). }
  assert (Hj'_in : In j' (candidates_of jobs 1 sched t)).
  { exact (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose). }
  (* Step 4: deadline(j') <= deadline(j_viol) < deadline(j) -- strict! *)
  assert (Hj'_le_viol : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j_viol)).
  { exact (choose_edf_min_deadline jobs 1 sched t _ j' Hchoose j_viol Hin_viol Helig_viol). }
  assert (Hj'_lt : job_abs_deadline (jobs j') < job_abs_deadline (jobs j)).
  { lia. }
  (* Step 5: j' <> j (different deadlines) *)
  assert (Hne : j' <> j).
  { intro Heqjj. subst j'. lia. }
  exists j'.
  split. exact Hj'_in.
  split. exact Hj'_elig.
  split. exact Hj'_lt.
  split. exact Hne.
  exact Hchoose.
Qed.

(* 18. repair_first_violation:
   Given a feasible valid schedule with an EDF violation at t0 (the first violation),
   produce a repaired schedule sched' = swap_at sched t0 t' that:
   - is still valid
   - is still feasible
   - agrees with sched strictly before t0
   - satisfies the canonical EDF match at t0
   Construction:
     j' = choose_edf result at t0 (canonical repair job, strictly earlier deadline)
     t' = time in [t0, deadline(j')) where j' runs in sched (exists by feasibility)
     sched' = swap_at sched t0 t'
   Fully constructive: no Classical. *)
Lemma repair_first_violation :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched (H : nat) t0 j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t0 < H ->
    sched t0 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t0 ->
    (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t) ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      agrees_before sched sched' t0 /\
      matches_choose_edf_at_with jobs candidates_of sched' t0.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched _H t0 j
         _HJbool Hvalid Hfeas _Ht0H Hsched Hviol _Hfirst.
  (* Step 1: extract J j from violation definition *)
  assert (HJj : J j).
  { unfold edf_violation_at_with, edf_violation_at_in in Hviol.
    destruct Hviol as [j0 [_j_viol [HJj0 [_HJviol [Hsched0 _]]]]].
    rewrite Hsched in Hsched0. injection Hsched0 as Heq. subst j0.
    exact HJj0. }
  (* Step 2: canonical repair job j' from Lemma 18' *)
  destruct (first_violation_yields_canonical_repair_job
              J candidates_of cand_spec jobs sched t0 j Hvalid Hsched HJj Hviol)
      as [j' [Hj'_in [Hj'_elig [Hj'_lt [_Hne Hchoose]]]]].
  (* Step 3: J j' from candidates_sound *)
  assert (HJj' : J j').
  { destruct cand_spec as [Hsound _ _].
    exact (Hsound jobs 1 sched t0 j' Hj'_in). }
  (* Step 4: t' where j' runs in sched, t0 <= t' < deadline(j') *)
  destruct (eligible_feasible_implies_runs_later_before_deadline
              J jobs sched j' t0 HJj' Hvalid Hfeas Hj'_elig)
      as [t' [Ht0_le [Ht'_lt Ht'_run]]].
  (* Step 5: agrees_before sched (swap_at sched t0 t') t0 *)
  assert (Hagree : agrees_before sched (swap_at sched t0 t') t0).
  { intros u c Hlt.
    symmetry.
    apply swap_at_same_outside.
    right. split; intro Heq; subst u; lia. }
  (* Step 6: produce sched' = swap_at sched t0 t' *)
  exists (swap_at sched t0 t').
  refine (conj _ (conj _ (conj _ _))).
  - (* valid_schedule *)
    exact (swap_at_preserves_valid_schedule jobs sched j j' t0 t'
             Hvalid Hsched Ht'_run Hj'_elig Ht0_le Hj'_lt).
  - (* feasible_schedule_on *)
    exact (swap_at_preserves_feasible_schedule_on J jobs sched j j' t0 t'
             Hvalid Hfeas HJj HJj' Hsched Ht'_run Hj'_elig Ht0_le Ht'_lt Hj'_lt).
  - (* agrees_before sched sched' t0 *)
    exact Hagree.
  - (* matches_choose_edf_at_with jobs candidates_of sched' t0 *)
    unfold matches_choose_edf_at_with, matches_choose_at_with.
    (* LHS: sched' t0 0 = swap_at sched t0 t' t0 0 = sched t' 0 = Some j' *)
    rewrite swap_at_t1.
    rewrite Ht'_run.
    (* RHS: choose_edf jobs 1 sched' t0 (candidates_of jobs 1 sched' t0) = Some j'
       Use agrees_before_sym + candidates_of_agrees_before + choose_edf_agrees_before *)
    assert (Hagree_sym : agrees_before (swap_at sched t0 t') sched t0).
    { exact (agrees_before_sym _ _ _ Hagree). }
    rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
               (swap_at sched t0 t') sched t0 Hagree_sym).
    rewrite (choose_edf_agrees_before jobs (swap_at sched t0 t') sched t0 _
               Hagree_sym).
    exact (eq_sym Hchoose).
Qed.

(* Finite-horizon normalization is now shared by the generic canonicalization
   skeleton in [SchedulingAlgorithmNormalization] and instantiated for EDF in
   [EDFOptimality].  This file intentionally stops at the local one-step repair
   interface used by [repair_non_canonical_at]. *)
