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
Require Import SchedulingAlgorithmNormalization.
Require Import SchedulingAlgorithmOptimalitySkeleton.
Require Import UniPolicies.MetricChooserLemmas.
Require Import UniPolicies.EDF.
Require Import UniPolicies.EDFLemmas.
Import ListNotations.

Definition is_canonical_at_b
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : bool :=
  match sched t 0, choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) with
  | None, None => true
  | Some j, Some j' => Nat.eqb j j'
  | _, _ => false
  end.

Lemma is_canonical_at_b_true_iff :
  forall candidates_of jobs sched t,
    is_canonical_at_b candidates_of jobs sched t = true <->
    matches_choose_edf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  unfold is_canonical_at_b, matches_choose_edf_at_with, matches_dispatch_at_with.
  simpl.
  destruct (sched t 0) as [j|] eqn:Es;
  destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Ec.
  - split.
    + intro H. apply Nat.eqb_eq in H. subst j'. reflexivity.
    + intro H. injection H as Heq. apply Nat.eqb_eq. exact Heq.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; reflexivity.
Qed.

Lemma is_canonical_at_b_false_iff :
  forall candidates_of jobs sched t,
    is_canonical_at_b candidates_of jobs sched t = false <->
    ~ matches_choose_edf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  rewrite <- is_canonical_at_b_true_iff.
  destruct (is_canonical_at_b candidates_of jobs sched t).
  - split; intro H; [discriminate | exact (False_ind _ (H eq_refl))].
  - split; intro H; [intro Hf; discriminate | reflexivity].
Qed.

Lemma repair_non_canonical_at :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j, sched t' 0 = Some j -> J j) ->
    single_cpu_only sched ->
    ~ matches_choose_edf_at_with jobs candidates_of sched t ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j, sched' t' 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_edf_at_with jobs candidates_of sched' t.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched t
         HJbool Hvalid Hfeas HJonly Hcpu1 Hnot.
  unfold matches_choose_edf_at_with, matches_dispatch_at_with in Hnot.
  simpl in Hnot.
  destruct (sched t 0) as [j|] eqn:Hst0.
  - destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + assert (Hne : j' <> j).
      { intro Heq. subst j'. apply Hnot. congruence. }
      assert (HJj : J j) by (exact (HJonly t j Hst0)).
      assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        exact (Hsound jobs 1 sched t j' (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose)). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by (exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose)).
      assert (Hdl_le : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
      { destruct cand_spec as [_ Hcomplete _].
        assert (Hin_j : In j (candidates_of jobs 1 sched t)).
        { apply Hcomplete. exact HJj. exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0). }
        exact (choose_edf_min_deadline jobs 1 sched t _ j' Hchoose j Hin_j
                 (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0)). }
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      exists (swap_at sched t t').
      assert (Hlt : t < t' \/ t = t').
      { destruct (Nat.eq_dec t t') as [-> | Hne']. right. reflexivity. left. lia. }
      assert (Hlt12 : t < t').
      { destruct Hlt as [H | Heq]. exact H.
        subst t'. rewrite Hst0 in Ht'_run. injection Ht'_run as Heqjj'.
        subst j. exfalso. exact (Hne eq_refl). }
      assert (Hagree : agrees_before sched (swap_at sched t t') t).
      { intros u c Hlu. symmetry.
        apply swap_at_same_outside. right. split; intro Heq; subst u; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact (swap_at_preserves_valid_schedule_ne jobs sched j j' t t'
                 Hvalid Hst0 Ht'_run Helig' (Nat.lt_le_incl t t' Hlt12)
                 (fun Heq => Hne (eq_sym Heq))).
      * exact (swap_at_preserves_feasible_schedule_on_le J jobs sched j j' t t'
                 Hvalid Hfeas HJj HJj' Hst0 Ht'_run Helig'
                 (Nat.lt_le_incl t t' Hlt12) Ht'_lt Hdl_le).
      * intros t'' j'' Hrun.
        destruct (Nat.eq_dec t'' t) as [-> | Ht''ne].
        -- rewrite swap_at_t1 in Hrun. rewrite Ht'_run in Hrun.
           injection Hrun as Heq. subst j''. exact HJj'.
        -- destruct (Nat.eq_dec t'' t') as [-> | Ht''ne'].
           ++ rewrite swap_at_t2 in Hrun. rewrite Hst0 in Hrun.
              injection Hrun as Heq. subst j''. exact HJj.
           ++ rewrite (swap_at_same_outside sched t t' t'' 0
                         (or_intror (conj Ht''ne Ht''ne'))) in Hrun.
              exact (HJonly t'' j'' Hrun).
      * exact (swap_at_single_cpu_only sched t t' Hcpu1).
      * exact Hagree.
      * unfold matches_choose_edf_at_with, matches_dispatch_at_with.
        simpl.
        rewrite swap_at_t1. rewrite Ht'_run.
        assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
          by (exact (agrees_before_sym _ _ _ Hagree)).
        rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
                   (swap_at sched t t') sched t Hagree_sym).
        rewrite (choose_edf_agrees_before jobs (swap_at sched t t') sched t _
                   Hagree_sym).
        exact (eq_sym Hchoose).
    + exfalso.
      assert (HJj : J j) by (exact (HJonly t j Hst0)).
      destruct cand_spec as [_ Hcomplete _].
      assert (Hin : In j (candidates_of jobs 1 sched t)).
      { apply Hcomplete. exact HJj. exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0). }
      assert (Helig : eligible jobs 1 sched j t)
        by exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0).
      destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t)
                  (ex_intro _ j (conj Hin Helig))) as [j'' Hsome].
      rewrite Hchoose in Hsome. discriminate.
  - destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        exact (Hsound jobs 1 sched t j' (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose)). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by (exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose)).
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      assert (Hlt12 : t < t').
      { destruct (Nat.eq_dec t t') as [-> | Hne].
        - rewrite Hst0 in Ht'_run. discriminate.
        - lia. }
      exists (swap_at sched t t').
      assert (Hagree : agrees_before sched (swap_at sched t t') t).
      { intros u c Hlu. symmetry.
        apply swap_at_same_outside. right. split; intro Heq; subst u; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact (swap_at_preserves_valid_schedule_none jobs sched j' t t'
                 Hvalid Hst0 Ht'_run Helig' Hlt12).
      * exact (swap_at_preserves_feasible_schedule_on_none J jobs sched j' t t'
                 Hfeas HJj' Hst0 Ht'_run Hlt12 Ht'_lt).
      * intros t'' j'' Hrun.
        destruct (Nat.eq_dec t'' t) as [-> | Ht''ne].
        -- rewrite swap_at_t1 in Hrun. rewrite Ht'_run in Hrun.
           injection Hrun as Heq. subst j''. exact HJj'.
        -- destruct (Nat.eq_dec t'' t') as [-> | Ht''ne'].
           ++ rewrite swap_at_t2 in Hrun. rewrite Hst0 in Hrun. discriminate.
           ++ rewrite (swap_at_same_outside sched t t' t'' 0
                         (or_intror (conj Ht''ne Ht''ne'))) in Hrun.
              exact (HJonly t'' j'' Hrun).
      * exact (swap_at_single_cpu_only sched t t' Hcpu1).
      * exact Hagree.
      * unfold matches_choose_edf_at_with, matches_dispatch_at_with.
        simpl.
        rewrite swap_at_t1. rewrite Ht'_run.
        assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
          by (exact (agrees_before_sym _ _ _ Hagree)).
        rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
                   (swap_at sched t t') sched t Hagree_sym).
        rewrite (choose_edf_agrees_before jobs (swap_at sched t t') sched t _
                   Hagree_sym).
        exact (eq_sym Hchoose).
    + exfalso. apply Hnot.
      unfold matches_choose_edf_at_with, matches_dispatch_at_with. congruence.
Qed.

Lemma edf_canonical_at_dec :
  forall candidates_of jobs sched t,
    {matches_choose_edf_at_with jobs candidates_of sched t} +
    {~ matches_choose_edf_at_with jobs candidates_of sched t}.
Proof.
  intros candidates_of jobs sched t.
  destruct (is_canonical_at_b candidates_of jobs sched t) eqn:Hb.
  - left. apply (is_canonical_at_b_true_iff candidates_of jobs sched t). exact Hb.
  - right. apply (is_canonical_at_b_false_iff candidates_of jobs sched t). exact Hb.
Qed.

Definition EDFCanonicalRepairSpec
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    (jobs : JobId -> Job) :
    CanonicalRepairSpec edf_generic_spec J candidates_of jobs.
  refine ({|
    canonical_at := fun sched t => matches_choose_edf_at_with jobs candidates_of sched t;
    canonical_before := fun sched H => matches_choose_edf_before jobs candidates_of sched H;
    canonical_before_def := fun sched H => conj (fun Hcanon => Hcanon) (fun Hcanon => Hcanon);
    canonical_at_def := fun sched t => conj (fun Hcanon => Hcanon) (fun Hcanon => Hcanon);
    canonical_at_dec := fun sched t => edf_canonical_at_dec candidates_of jobs sched t;
    repair_non_canonical := fun J_bool sched t HJbool Hvalid Hfeas HJonly Hcpu Hnot =>
      repair_non_canonical_at J J_bool candidates_of cand_spec jobs sched t
        HJbool Hvalid Hfeas HJonly Hcpu Hnot
  |}).
Defined.

Lemma edf_normalize_to_canonical :
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
      matches_choose_edf_before jobs candidates_of sched' H.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H HJbool Hvalid Hfeas HJonly Hcpu.
  eapply normalize_to_canonical_generic with
      (alg := edf_generic_spec)
      (J_bool := J_bool)
      (sched := sched).
  - exact (EDFCanonicalRepairSpec J candidates_of cand_spec jobs).
  - intros s1 s2 t Hagree.
    exact (edf_dispatch_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact HJbool.
  - exact Hvalid.
  - exact Hfeas.
  - exact HJonly.
  - exact Hcpu.
Qed.

Theorem edf_optimality_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (edf_scheduler candidates_of) jobs 1.
Proof.
  intros J J_bool enumJ candidates_of cand_spec jobs
         HJbool HJ_in _HJ_complete Hfeas_on.
  change (schedulable_by_on
            J
            (single_cpu_algorithm_scheduler_on J edf_generic_spec candidates_of cand_spec)
            jobs 1).
  eapply finite_optimality_via_normalization.
  - exact HJbool.
  - exact HJ_in.
  - intros sched0 H Hvalid Hfeas HJonly Hcpu.
    exact (edf_normalize_to_canonical J J_bool candidates_of cand_spec jobs sched0 H
             HJbool Hvalid Hfeas HJonly Hcpu).
  - intros s1 s2 t Hagree.
    exact (edf_dispatch_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  - exact Hfeas_on.
Qed.
