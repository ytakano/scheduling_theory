From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleTransform.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Require Import UniPolicies.MetricChooserLemmas.
Import ListNotations.

Definition trunc_sched (sched : Schedule) (H : nat) : Schedule :=
  fun t c => if t <? H then sched t c else None.

Lemma trunc_sched_before :
  forall sched H t c,
    t < H ->
    trunc_sched sched H t c = sched t c.
Proof.
  intros sched H t c Hlt.
  unfold trunc_sched.
  assert (Hltb : (t <? H) = true) by (apply Nat.ltb_lt; exact Hlt).
  now rewrite Hltb.
Qed.

Lemma trunc_sched_after :
  forall sched H t c,
    H <= t ->
    trunc_sched sched H t c = None.
Proof.
  intros sched H t c Hle.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Lemma trunc_sched_single_cpu_only :
  forall sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H).
Proof.
  intros sched H Honly t c Hc.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - exact (Honly t c Hc).
  - reflexivity.
Qed.

Lemma trunc_sched_agrees_before :
  forall sched H,
    agrees_before (trunc_sched sched H) sched H.
Proof.
  intros sched H t c Hlt.
  apply trunc_sched_before.
  exact Hlt.
Qed.

Lemma trunc_sched_valid :
  forall jobs sched H,
    valid_schedule jobs 1 sched ->
    valid_schedule jobs 1 (trunc_sched sched H).
Proof.
  intros jobs sched H Hvalid j t c Hc Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  destruct (lt_dec t H) as [Hlt | Hge].
  - rewrite (trunc_sched_before sched H t 0 Hlt) in Hrun.
    assert (Helig : eligible jobs 1 sched j t) by exact (Hvalid j t 0 Hc Hrun).
    split.
    + exact (proj1 Helig).
    + intro Hcomp. apply (proj2 Helig). unfold completed in *.
      assert (Heq :
                service_job 1 (trunc_sched sched H) j t =
                service_job 1 sched j t).
      { apply service_job_eq_of_cpu_count_eq.
        intros t' Hlt'.
        destruct (lt_dec t' H) as [Hlt'' | Hge''].
        - simpl. unfold runs_on.
          rewrite (trunc_sched_before sched H t' 0 Hlt'').
          reflexivity.
        - exfalso. lia. }
      rewrite Heq in Hcomp.
      exact Hcomp.
  - rewrite (trunc_sched_after sched H t 0 (proj1 (Nat.nlt_ge t H) Hge)) in Hrun.
    discriminate.
Qed.

Lemma trunc_sched_feasible :
  forall J jobs sched H,
    feasible_schedule_on J jobs 1 sched ->
    (forall j, J j -> job_abs_deadline (jobs j) <= H) ->
    feasible_schedule_on J jobs 1 (trunc_sched sched H).
Proof.
  intros J jobs sched H Hfeas Hdl_le j HJj Hmiss.
  apply (Hfeas j HJj).
  unfold missed_deadline in *. unfold completed in *.
  assert (Heq :
            service_job 1 (trunc_sched sched H) j (job_abs_deadline (jobs j)) =
            service_job 1 sched j (job_abs_deadline (jobs j))).
  { apply service_job_eq_of_cpu_count_eq.
    intros t Hlt.
    destruct (lt_dec t H) as [Hlt' | Hge'].
    - simpl. unfold runs_on.
      rewrite (trunc_sched_before sched H t 0 Hlt').
      reflexivity.
    - assert (Hge : H <= t) by lia.
      assert (Hdl : job_abs_deadline (jobs j) <= H) by exact (Hdl_le j HJj).
      assert (job_abs_deadline (jobs j) <= t) by lia.
      lia. }
  rewrite <- Heq.
  exact Hmiss.
Qed.

Lemma trunc_sched_preserves_canonical_before :
  forall alg J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall s1 s2 t,
        agrees_before s1 s2 t ->
        dispatch alg jobs 1 s1 t (candidates_of jobs 1 s1 t) =
        dispatch alg jobs 1 s2 t (candidates_of jobs 1 s2 t)) ->
    matches_dispatch_before alg jobs candidates_of sched H ->
    matches_dispatch_before alg jobs candidates_of (trunc_sched sched H) H.
Proof.
  intros alg J candidates_of cand_spec jobs sched H Hdispatch Hcanon.
  unfold matches_dispatch_before, matches_dispatch_at_with.
  intros t Hlt.
  rewrite (trunc_sched_before sched H t 0 Hlt).
  assert (Hagree : agrees_before (trunc_sched sched H) sched t).
  { apply agrees_before_weaken with H.
    - lia.
    - apply trunc_sched_agrees_before. }
  rewrite (Hdispatch (trunc_sched sched H) sched t Hagree).
  exact (Hcanon t Hlt).
Qed.
