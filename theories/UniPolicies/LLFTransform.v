From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
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
Import ListNotations.

Lemma sequential_jobs_single_cpu :
  forall sched,
    sequential_jobs 1 sched.
Proof.
  intros sched j t c1 c2 Hc1 Hc2 _ _. lia.
Qed.

Lemma service_job_increase_at_most_length_uni :
  forall sched j t1 t2,
    t1 <= t2 ->
    service_job 1 sched j t2 <= service_job 1 sched j t1 + (t2 - t1).
Proof.
  intros sched j t1 t2 Hle.
  revert t1 Hle.
  induction t2 as [|t2 IH]; intros t1 Hle.
  - assert (t1 = 0) by lia. subst. simpl. lia.
  - destruct (Nat.eq_dec t1 (S t2)) as [-> | Hneq].
    + rewrite Nat.sub_diag. lia.
    + assert (Hle' : t1 <= t2) by lia.
      pose proof (IH t1 Hle') as Hih.
      pose proof (service_job_increase_at_most_1 1 sched j t2 (sequential_jobs_single_cpu sched)) as Hstep.
      lia.
Qed.

Lemma llf_candidate_runs_before_both_deadlines :
  forall J jobs sched j j' t,
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    J j' ->
    sched t 0 = Some j ->
    j' <> j ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z ->
    exists t',
      t <= t' /\
      t' < job_abs_deadline (jobs j) /\
      t' < job_abs_deadline (jobs j') /\
      sched t' 0 = Some j'.
Proof.
  intros J jobs sched j j' t Hvalid Hfeas HJj HJj' Hrun Hneq Helig' Hllf.
  assert (Helig_j : eligible jobs 1 sched j t).
  { exact (valid_running_implies_eligible jobs 1 sched j t 0 Hvalid (Nat.lt_succ_diag_r 0) Hrun). }
  destruct (le_lt_dec (job_abs_deadline (jobs j')) (job_abs_deadline (jobs j)))
    as [Hdl_le | Hdl_lt].
  - destruct (eligible_feasible_implies_runs_later_before_deadline
                J jobs sched j' t HJj' Hvalid Hfeas Helig')
      as [t' [Hle [Hlt' Hrun']]].
    exists t'. repeat split; try exact Hle; try exact Hrun'; lia.
  - assert (Ht_lt_dj : t < job_abs_deadline (jobs j)).
    { destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j t HJj Hvalid Hfeas Helig_j)
        as [u [Htu [Hud _Hrunu]]].
      lia. }
    assert (Hncomp_j : ~ completed jobs 1 sched j t) by exact (proj2 Helig_j).
    assert (Hrem_j_pos : remaining_cost jobs 1 sched j t > 0).
    { exact (not_completed_implies_remaining_cost_pos jobs 1 sched j t Hncomp_j). }
    assert (Hgap : (job_abs_deadline (jobs j') - job_abs_deadline (jobs j)
                    < remaining_cost jobs 1 sched j' t)%nat).
    { rewrite !laxity_unfold in Hllf. unfold remaining_cost in *. lia. }
    assert (Hcost_le_deadline :
              job_cost (jobs j') <=
              service_job 1 sched j' (job_abs_deadline (jobs j'))).
    { destruct (le_lt_dec (job_cost (jobs j'))
                          (service_job 1 sched j' (job_abs_deadline (jobs j'))))
        as [Hle | Hlt].
      - exact Hle.
      - exfalso. apply (Hfeas j' HJj').
        rewrite missed_deadline_iff_service_lt_cost_at_deadline.
        exact Hlt. }
    assert (Hafter_bound :
              service_job 1 sched j' (job_abs_deadline (jobs j')) <=
              service_job 1 sched j' (job_abs_deadline (jobs j)) +
              (job_abs_deadline (jobs j') - job_abs_deadline (jobs j))).
    { apply (service_job_increase_at_most_length_uni sched j'
               (job_abs_deadline (jobs j)) (job_abs_deadline (jobs j'))).
      lia. }
    assert (Hinc : service_job 1 sched j' t < service_job 1 sched j' (job_abs_deadline (jobs j))).
    { unfold remaining_cost in Hgap. lia. }
    destruct (service_increases_implies_executed_in_interval
                1 sched j' t (job_abs_deadline (jobs j)) Ht_lt_dj Hinc)
      as [t' [[Hle Hlt] Hcpu]].
    apply cpu_count_pos_iff_executed in Hcpu.
    destruct Hcpu as [c [Hc Hrun']].
    assert (Hc0 : c = 0) by lia. subst c.
    exists t'. repeat split; try exact Hle; try exact Hlt; try exact Hrun'; lia.
Qed.

Lemma swap_at_preserves_feasible_schedule_on_before_both_deadlines :
  forall J jobs sched j j' t t',
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    J j' ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    t' < job_abs_deadline (jobs j) ->
    t' < job_abs_deadline (jobs j') ->
    feasible_schedule_on J jobs 1 (swap_at sched t t').
Proof.
  intros J jobs sched j j' t t' Hfeas HJj HJj' Hj Hj' Hle Hlt_j Hlt_j'.
  unfold feasible_schedule_on.
  intros x HJx.
  destruct (Nat.eq_dec x j') as [-> | Hxj'].
  - apply (swap_at_improves_front_job jobs sched j j' t t' Hle Hlt_j' Hj Hj').
    exact (Hfeas j' HJj').
  - destruct (Nat.eq_dec x j) as [-> | Hxj].
    + apply (swap_at_does_not_hurt_later_deadline_job jobs sched j j' t t' Hle Hlt_j Hj Hj').
      exact (Hfeas j HJj).
    + rewrite (swap_at_preserves_missed_deadline_other_job jobs sched j j' t t' x Hj Hj' Hxj Hxj').
      exact (Hfeas x HJx).
Qed.

Lemma repair_non_canonical_at_llf_common :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j j',
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j0, sched t' 0 = Some j0 -> J j0) ->
    single_cpu_only sched ->
    sched t 0 = Some j ->
    choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j' ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z ->
    j' <> j ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j0, sched' t' 0 = Some j0 -> J j0) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_llf_at_with jobs candidates_of sched' t.
Proof.
  intros J candidates_of cand_spec jobs sched t j j'
         Hvalid Hfeas HJonly Hcpu1 Hrun Hchoose Helig' Hle Hneq.
  assert (HJj : J j) by (exact (HJonly t j Hrun)).
  assert (HJj' : J j').
  { destruct cand_spec as [Hsound _ _].
    apply (Hsound jobs 1 sched t j').
    exact (choose_llf_in_candidates jobs 1 sched t _ j' Hchoose). }
  destruct (llf_candidate_runs_before_both_deadlines
              J jobs sched j j' t Hvalid Hfeas HJj HJj' Hrun Hneq Helig' Hle)
    as [t' [Htt' [Hlt_j [Hlt_j' Hrun']]]].
  exists (swap_at sched t t').
  assert (Hagree : agrees_before sched (swap_at sched t t') t).
  { intros u c Hlt.
    symmetry.
    apply swap_at_same_outside.
    right. split; intro Heq; subst u; lia. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact (swap_at_preserves_valid_schedule_ne jobs sched j j' t t'
             Hvalid Hrun Hrun' Helig' Htt' (fun Heq => Hneq (eq_sym Heq))).
  - exact (swap_at_preserves_feasible_schedule_on_before_both_deadlines
             J jobs sched j j' t t' Hfeas HJj HJj' Hrun Hrun' Htt' Hlt_j Hlt_j').
  - intros t'' j0 Hrun0.
    destruct (Nat.eq_dec t'' t) as [-> | Htne].
    + rewrite swap_at_t1 in Hrun0. rewrite Hrun' in Hrun0.
      injection Hrun0 as Heq. subst j0. exact HJj'.
    + destruct (Nat.eq_dec t'' t') as [-> | Ht'ne].
      * rewrite swap_at_t2 in Hrun0. rewrite Hrun in Hrun0.
        injection Hrun0 as Heq. subst j0. exact HJj.
      * rewrite (swap_at_same_outside sched t t' t'' 0 (or_intror (conj Htne Ht'ne))) in Hrun0.
        exact (HJonly t'' j0 Hrun0).
  - exact (swap_at_single_cpu_only sched t t' Hcpu1).
  - exact Hagree.
  - unfold matches_choose_llf_at_with, matches_dispatch_at_with.
    simpl.
    rewrite swap_at_t1. rewrite Hrun'.
    assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
      by exact (agrees_before_sym _ _ _ Hagree).
    rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
               (swap_at sched t t') sched t Hagree_sym).
    rewrite (choose_llf_agrees_before jobs (swap_at sched t t') sched t _ Hagree_sym).
    exact (eq_sym Hchoose).
Qed.

Lemma repair_non_canonical_at_llf_tie :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j j',
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j0, sched t' 0 = Some j0 -> J j0) ->
    single_cpu_only sched ->
    sched t 0 = Some j ->
    choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j' ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j' t = laxity jobs 1 sched j t)%Z ->
    j' <> j ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j0, sched' t' 0 = Some j0 -> J j0) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_llf_at_with jobs candidates_of sched' t.
Proof.
  intros J candidates_of cand_spec jobs sched t j j'
         Hvalid Hfeas HJonly Hcpu1 Hrun Hchoose Helig' Heq Hneq.
  eapply repair_non_canonical_at_llf_common; eauto.
  lia.
Qed.

Lemma repair_non_canonical_at_llf_strict :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j j',
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j0, sched t' 0 = Some j0 -> J j0) ->
    single_cpu_only sched ->
    sched t 0 = Some j ->
    choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j' ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j' t < laxity jobs 1 sched j t)%Z ->
    j' <> j ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j0, sched' t' 0 = Some j0 -> J j0) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_llf_at_with jobs candidates_of sched' t.
Proof.
  intros J candidates_of cand_spec jobs sched t j j'
         Hvalid Hfeas HJonly Hcpu1 Hrun Hchoose Helig' Hlt Hneq.
  eapply repair_non_canonical_at_llf_common; eauto.
  lia.
Qed.

Lemma repair_non_canonical_at_llf :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j, sched t' 0 = Some j -> J j) ->
    single_cpu_only sched ->
    ~ matches_choose_llf_at_with jobs candidates_of sched t ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j, sched' t' 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_llf_at_with jobs candidates_of sched' t.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched t
         _HJbool Hvalid Hfeas HJonly Hcpu1 Hnot.
  destruct (sched t 0) as [j|] eqn:Hst0.
  - assert (HJj : J j) by (exact (HJonly t j Hst0)).
    destruct (canonical_non_llf_step_has_other_min_or_better_eligible_job
                J candidates_of cand_spec jobs sched t j
                Hvalid Hst0 HJj Hnot)
      as [j' [Hin [Helig' [Hle [Hneq Hchoose]]]]].
    destruct (Z.eq_dec (laxity jobs 1 sched j' t) (laxity jobs 1 sched j t)) as [Heq | Hneq_lax].
    + eapply repair_non_canonical_at_llf_tie; eauto.
    + eapply repair_non_canonical_at_llf_strict; eauto. lia.
  - destruct (choose_llf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        apply (Hsound jobs 1 sched t j').
        exact (choose_llf_in_candidates jobs 1 sched t _ j' Hchoose). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by exact (choose_llf_eligible jobs 1 sched t _ j' Hchoose).
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
        as [t' [Htt' [Hlt' Hrun']]].
      assert (Htt'_lt : t < t').
      { destruct (Nat.eq_dec t t') as [-> | Hne].
        - rewrite Hst0 in Hrun'. discriminate.
        - lia. }
      exists (swap_at sched t t').
      assert (Hagree : agrees_before sched (swap_at sched t t') t).
      { intros u c Hlt.
        symmetry.
        apply swap_at_same_outside.
        right. split; intro Heq; subst u; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact (swap_at_preserves_valid_schedule_none jobs sched j' t t'
                 Hvalid Hst0 Hrun' Helig' Htt'_lt).
      * exact (swap_at_preserves_feasible_schedule_on_none J jobs sched j' t t'
                 Hfeas HJj' Hst0 Hrun' Htt'_lt Hlt').
      * intros t'' j0 Hrun0.
        destruct (Nat.eq_dec t'' t) as [-> | Htne].
        -- rewrite swap_at_t1 in Hrun0. rewrite Hrun' in Hrun0.
           injection Hrun0 as Heq. subst j0. exact HJj'.
        -- destruct (Nat.eq_dec t'' t') as [-> | Ht'ne].
           ++ rewrite swap_at_t2 in Hrun0. rewrite Hst0 in Hrun0. discriminate.
           ++ rewrite (swap_at_same_outside sched t t' t'' 0 (or_intror (conj Htne Ht'ne))) in Hrun0.
              exact (HJonly t'' j0 Hrun0).
      * exact (swap_at_single_cpu_only sched t t' Hcpu1).
      * exact Hagree.
      * unfold matches_choose_llf_at_with, matches_dispatch_at_with.
        simpl.
        rewrite swap_at_t1. rewrite Hrun'.
        assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
          by exact (agrees_before_sym _ _ _ Hagree).
        rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
                   (swap_at sched t t') sched t Hagree_sym).
        rewrite (choose_llf_agrees_before jobs (swap_at sched t t') sched t _ Hagree_sym).
        exact (eq_sym Hchoose).
    + exfalso.
      apply Hnot.
      unfold matches_choose_llf_at_with, matches_dispatch_at_with.
      simpl.
      rewrite Hst0.
      exact (eq_sym Hchoose).
Qed.
