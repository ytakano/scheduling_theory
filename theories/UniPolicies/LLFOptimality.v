From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleTransform.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Require Import UniPolicies.MetricChooserLemmas.
Require Import UniPolicies.LLF.
Require Import UniPolicies.LLFLemmas.
Require Import UniPolicies.LLFTransform.
Import ListNotations.

(* ===== Section 8: Strong normalization ===== *)

Lemma repair_pushes_first_violation_forward_llf :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched sched' t0,
    single_cpu_only sched ->
    single_cpu_only sched' ->
    agrees_before sched sched' t0 ->
    matches_choose_llf_at_with jobs candidates_of sched' t0 ->
    matches_choose_llf_before jobs candidates_of sched t0 ->
    matches_choose_llf_before jobs candidates_of sched' (S t0).
Proof.
  intros J candidates_of cand_spec jobs sched sched' t0
         Honly Honly' Hagree Hmatch Hbefore.
  unfold matches_choose_llf_before, matches_dispatch_before.
  intros t Hlt.
  assert (Hcases : t < t0 \/ t = t0) by lia.
  destruct Hcases as [Hlt' | Heq].
  - unfold matches_choose_llf_at_with, matches_dispatch_at_with.
    simpl.
    specialize (Hbefore t Hlt').
    unfold matches_choose_llf_at_with, matches_dispatch_at_with in Hbefore.
    simpl in Hbefore.
    assert (Hpre : agrees_before sched sched' t).
    { apply (agrees_before_weaken sched sched' t t0). lia. exact Hagree. }
    assert (Hpre_sym : agrees_before sched' sched t)
      by (exact (agrees_before_sym _ _ _ Hpre)).
    assert (Hs't0 : sched' t 0 = sched t 0)
      by (symmetry; exact (Hagree t 0 Hlt')).
    assert (Hcand_eq : candidates_of jobs 1 sched' t = candidates_of jobs 1 sched t).
    { apply (candidates_prefix_extensional J candidates_of cand_spec jobs 1 sched' sched t).
      intros t' c Hlt''.
      destruct (Nat.eq_dec c 0) as [-> | Hcne].
      - symmetry. exact (Hpre t' 0 Hlt'').
      - assert (Hcpos : 0 < c) by lia.
        rewrite (Honly' t' c Hcpos). rewrite (Honly t' c Hcpos). reflexivity. }
    assert (Hchoose_eq : choose_llf jobs 1 sched' t (candidates_of jobs 1 sched' t) =
                         choose_llf jobs 1 sched t (candidates_of jobs 1 sched t)).
    { rewrite Hcand_eq.
      apply (choose_llf_agrees_before jobs sched' sched t (candidates_of jobs 1 sched t)).
      exact Hpre_sym. }
    rewrite Hs't0. rewrite Hchoose_eq. exact Hbefore.
  - subst t. exact Hmatch.
Qed.

Lemma llf_normalize_to_canonical :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t j, sched t 0 = Some j -> J j) ->
    single_cpu_only sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t j, sched' t 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      matches_choose_llf_before jobs candidates_of sched' H.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H HJbool.
  induction H as [| H' IH].
  - intros Hvalid Hfeas HJonly Hcpu1.
    exists sched.
    refine (conj Hvalid (conj Hfeas (conj HJonly (conj Hcpu1 _)))).
    unfold matches_choose_llf_before, matches_dispatch_before.
    intros t Hlt. lia.
  - intros Hvalid Hfeas HJonly Hcpu1.
    destruct (IH Hvalid Hfeas HJonly Hcpu1)
      as [sched_ih [Hih_valid [Hih_feas [Hih_Jonly [Hih_cpu1 Hih_canon]]]]].
    destruct (is_llf_canonical_at_b candidates_of jobs sched_ih H') eqn:Hb.
    + exists sched_ih.
      refine (conj Hih_valid (conj Hih_feas (conj Hih_Jonly (conj Hih_cpu1 _)))).
      unfold matches_choose_llf_before, matches_dispatch_before.
      intros t Hlt.
      assert (Hcases : t < H' \/ t = H') by lia.
      destruct Hcases as [Hlt' | Heq].
      * exact (Hih_canon t Hlt').
      * subst t.
        apply (is_llf_canonical_at_b_true_iff candidates_of jobs sched_ih H').
        exact Hb.
    + assert (Hnot : ~ matches_choose_llf_at_with jobs candidates_of sched_ih H').
      { apply (is_llf_canonical_at_b_false_iff candidates_of jobs sched_ih H'). exact Hb. }
      destruct (repair_non_canonical_at_llf J J_bool candidates_of cand_spec
                   jobs sched_ih H'
                   HJbool Hih_valid Hih_feas Hih_Jonly Hih_cpu1 Hnot)
        as [sched_r [Hr_valid [Hr_feas [Hr_Jonly [Hr_cpu1 [Hr_agree Hr_match]]]]]].
      exists sched_r.
      refine (conj Hr_valid (conj Hr_feas (conj Hr_Jonly (conj Hr_cpu1 _)))).
      exact (repair_pushes_first_violation_forward_llf
               J candidates_of cand_spec
               jobs sched_ih sched_r H'
               Hih_cpu1 Hr_cpu1 Hr_agree Hr_match Hih_canon).
Qed.

Lemma llf_normalize_up_to :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t j, sched t 0 = Some j -> J j) ->
    single_cpu_only sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t, t < H -> matches_choose_llf_at_with jobs candidates_of sched' t).
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H
         HJbool Hvalid Hfeas HJonly Hcpu1.
  destruct (llf_normalize_to_canonical
              J J_bool candidates_of cand_spec jobs sched H
              HJbool Hvalid Hfeas HJonly Hcpu1)
    as [sched' [Hvalid' [Hfeas' [_HJonly' [_Hcpu1' Hcanon]]]]].
  exists sched'.
  split. exact Hvalid'.
  split. exact Hfeas'.
  exact Hcanon.
Qed.

(* ===== Section 9: Truncation ===== *)

Definition trunc_sched (sched : Schedule) (H : nat) : Schedule :=
  fun t c => if t <? H then sched t c else None.

Lemma trunc_sched_before : forall sched H t c,
    t < H -> trunc_sched sched H t c = sched t c.
Proof.
  intros sched H t c Hlt.
  unfold trunc_sched.
  assert (E : (t <? H) = true) by (apply Nat.ltb_lt; exact Hlt).
  rewrite E. reflexivity.
Qed.

Lemma trunc_sched_after : forall sched H t c,
    H <= t -> trunc_sched sched H t c = None.
Proof.
  intros sched H t c Hle.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Lemma trunc_sched_single_cpu_only : forall sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H).
Proof.
  intros sched H Honly t c Hc.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - exact (Honly t c Hc).
  - reflexivity.
Qed.

Lemma trunc_sched_valid : forall jobs sched H,
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
      assert (Heq : service_job 1 (trunc_sched sched H) j t =
                    service_job 1 sched j t).
      { apply service_job_eq_of_cpu_count_eq. intros t'' Hlt''.
        destruct (lt_dec t'' H) as [Hlt''' | Hge'''].
        - simpl. unfold runs_on. rewrite (trunc_sched_before sched H t'' 0 Hlt'''). reflexivity.
        - exfalso. lia. }
      rewrite Heq in Hcomp. exact Hcomp.
  - rewrite (trunc_sched_after sched H t 0 (proj1 (Nat.nlt_ge t H) Hge)) in Hrun.
    discriminate.
Qed.

Lemma trunc_sched_feasible : forall J jobs sched H,
    (forall j, J j -> job_abs_deadline (jobs j) <= H) ->
    feasible_schedule_on J jobs 1 sched ->
    feasible_schedule_on J jobs 1 (trunc_sched sched H).
Proof.
  intros J jobs sched H Hdl_le Hfeas j HJj Hmiss.
  apply (Hfeas j HJj).
  unfold missed_deadline in *. unfold completed in *.
  assert (Heq : service_job 1 (trunc_sched sched H) j (job_abs_deadline (jobs j)) =
                service_job 1 sched j (job_abs_deadline (jobs j))).
  { apply service_job_eq_of_cpu_count_eq. intros t Hlt.
    destruct (lt_dec t H) as [Hlt' | Hge'].
    - simpl. unfold runs_on. rewrite (trunc_sched_before sched H t 0 Hlt'). reflexivity.
    - assert (Hge : H <= t) by lia.
      assert (Hdl : job_abs_deadline (jobs j) <= H) by (exact (Hdl_le j HJj)).
      assert (HH : job_abs_deadline (jobs j) <= t) by lia.
      lia. }
  rewrite <- Heq. exact Hmiss.
Qed.

Lemma trunc_sched_llf_canonical :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H) ->
    matches_choose_llf_before jobs candidates_of sched H ->
    matches_choose_llf_before jobs candidates_of (trunc_sched sched H) H.
Proof.
  intros J candidates_of cand_spec jobs sched H Honly Htrunc_only Hcanon.
  unfold matches_choose_llf_before, matches_dispatch_before,
         matches_choose_llf_at_with, matches_dispatch_at_with.
  simpl.
  intros t Hlt.
  rewrite (trunc_sched_before sched H t 0 Hlt).
  assert (Hagree : agrees_before (trunc_sched sched H) sched t).
  { intros t' c Hlt''.
    rewrite (trunc_sched_before sched H t' c (Nat.lt_trans t' t H Hlt'' Hlt)).
    reflexivity. }
  assert (Hagree_sym : agrees_before sched (trunc_sched sched H) t)
    by (exact (agrees_before_sym _ _ _ Hagree)).
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
             (trunc_sched sched H) sched t Hagree).
  rewrite (choose_llf_agrees_before jobs (trunc_sched sched H) sched t _
             Hagree).
  exact (Hcanon t Hlt).
Qed.

(* ===== Section 10: Bridge to scheduler_rel ===== *)

Lemma canonical_and_idle_implies_scheduler_rel_llf :
  forall J enumJ (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_choose_llf_before jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (llf_scheduler candidates_of) jobs 1 sched.
Proof.
  intros J enumJ candidates_of cand_spec jobs sched
         HJ_in Hvalid Hfeas Honly Hcanon Hidle.
  unfold llf_scheduler.
  eapply canonical_and_idle_implies_scheduler_rel_generic; eauto.
Qed.

(* ===== Section 11: Main theorem ===== *)

Theorem llf_optimality_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (llf_scheduler candidates_of) jobs 1.
Proof.
  intros J J_bool enumJ candidates_of cand_spec jobs
         HJbool HJ_in HJ_complete Hfeas_on.
  destruct Hfeas_on as [sched0 [Hvalid0 Hfeas0]].
  set (sched1 := J_restrict J_bool (mk_single_cpu sched0)).
  assert (Hvalid1 : valid_schedule jobs 1 sched1).
  { unfold sched1.
    apply (J_restrict_valid J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_valid jobs sched0 Hvalid0). }
  assert (Hfeas1 : feasible_schedule_on J jobs 1 sched1).
  { unfold sched1.
    apply (J_restrict_feasible J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_feasible J jobs sched0 Hfeas0). }
  assert (HJonly1 : forall t j, sched1 t 0 = Some j -> J j).
  { intros t j Hrun. unfold sched1 in Hrun.
    exact (J_restrict_J_only J_bool J (mk_single_cpu sched0) t j HJbool Hrun). }
  assert (Hcpu1 : single_cpu_only sched1).
  { unfold sched1. exact (J_restrict_only J_bool (mk_single_cpu sched0)). }
  set (H := deadline_horizon jobs enumJ).
  destruct (llf_normalize_to_canonical J J_bool candidates_of cand_spec jobs sched1 H
               HJbool Hvalid1 Hfeas1 HJonly1 Hcpu1)
    as [sched2 [Hvalid2 [Hfeas2 [HJonly2 [Hcpu2 Hcanon2]]]]].
  set (sched3 := trunc_sched sched2 H).
  assert (Hvalid3 : valid_schedule jobs 1 sched3)
    by (unfold sched3; exact (trunc_sched_valid jobs sched2 H Hvalid2)).
  assert (Hfeas3 : feasible_schedule_on J jobs 1 sched3).
  { unfold sched3.
    apply (trunc_sched_feasible J jobs sched2 H).
    - intros j HJj. apply Nat.lt_le_incl.
      unfold H. exact (J_implies_deadline_lt_horizon J enumJ jobs j HJ_in HJj).
    - exact Hfeas2. }
  assert (Hcpu3 : single_cpu_only sched3).
  { unfold sched3. exact (trunc_sched_single_cpu_only sched2 H Hcpu2). }
  assert (Hcanon3 : matches_choose_llf_before jobs candidates_of sched3 H).
  { unfold sched3.
    exact (trunc_sched_llf_canonical J candidates_of cand_spec jobs sched2 H
             Hcpu2 (trunc_sched_single_cpu_only sched2 H Hcpu2) Hcanon2). }
  assert (Hidle3 : forall t, H <= t -> sched3 t 0 = None).
  { intros t Hle. unfold sched3.
    exact (trunc_sched_after sched2 H t 0 Hle). }
  assert (Hrel : scheduler_rel (llf_scheduler candidates_of) jobs 1 sched3).
  { exact (canonical_and_idle_implies_scheduler_rel_llf J enumJ candidates_of cand_spec
             jobs sched3 HJ_in Hvalid3 Hfeas3 Hcpu3 Hcanon3 Hidle3). }
  exact (single_cpu_algorithm_schedulable_by_on_intro J llf_generic_spec candidates_of
           cand_spec jobs sched3 Hrel Hfeas3).
Qed.
