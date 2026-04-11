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
Require Import UniPolicies.EDF.
Require Import UniPolicies.EDFLemmas.
Require Import UniPolicies.EDFTransform.
Import ListNotations.

(* ===== Section 8: Strong normalization ===== *)

(* Boolean: is the schedule canonical at time t? *)
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

(* Repair lemma: if not canonical at t, produce a schedule that:
   - is still valid and feasible
   - agrees before t (so invariants from t' < t are preserved)
   - matches choose_edf at t
   Requires: J-only invariant (all running jobs are in J). *)
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
  (* Case split on sched t 0 *)
  destruct (sched t 0) as [j|] eqn:Hst0.
  - (* sched t 0 = Some j *)
    (* choose_edf must return Some j' with j' ≠ j *)
    destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + (* choose_edf = Some j'; j' ≠ j *)
      assert (Hne : j' <> j).
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
      (* Find t' where j' runs in sched, t <= t' < deadline(j') *)
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      exists (swap_at sched t t').
      assert (Hlt : t < t' \/ t = t').
      { destruct (Nat.eq_dec t t') as [-> | Hne']. right. reflexivity. left. lia. }
      (* If t = t': sched t 0 = Some j but sched t' 0 = sched t 0 = Some j,
         j' must = j (since Ht'_run : sched t' 0 = Some j'), but j' ≠ j. Contradiction. *)
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
      * (* J-only preserved *)
        intros t'' j'' Hrun.
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
    + (* choose_edf = None: impossible since j is eligible and J j *)
      exfalso.
      assert (HJj : J j) by (exact (HJonly t j Hst0)).
      destruct cand_spec as [_ Hcomplete _].
      assert (Hin : In j (candidates_of jobs 1 sched t)).
      { apply Hcomplete. exact HJj. exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0). }
      assert (Helig : eligible jobs 1 sched j t)
        by exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0).
      destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t)
                  (ex_intro _ j (conj Hin Helig))) as [j'' Hsome].
      rewrite Hchoose in Hsome. discriminate.
  - (* sched t 0 = None *)
    (* choose_edf must return Some j' (otherwise canonical) *)
    destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + (* choose_edf = Some j' *)
      assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        exact (Hsound jobs 1 sched t j' (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose)). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by (exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose)).
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      (* t ≤ t' and t ≠ t' since sched t 0 = None but sched t' 0 = Some j' *)
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
    + (* choose_edf = None and sched t 0 = None → canonical *)
      exfalso. apply Hnot.
      unfold matches_choose_edf_at_with, matches_dispatch_at_with. congruence.
Qed.

(* Propagation: repairing at t0 preserves canonical before t0. *)
Lemma repair_pushes_canonical_forward :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched sched' t0,
    single_cpu_only sched ->
    single_cpu_only sched' ->
    agrees_before sched sched' t0 ->
    matches_choose_edf_at_with jobs candidates_of sched' t0 ->
    matches_choose_edf_before jobs candidates_of sched t0 ->
    matches_choose_edf_before jobs candidates_of sched' (S t0).
Proof.
  intros J candidates_of cand_spec jobs sched sched' t0
         Honly Honly' Hagree Hmatch Hbefore.
  unfold matches_choose_edf_before, matches_dispatch_before.
  intros t Hlt.
  assert (Hcases : t < t0 \/ t = t0) by lia.
  destruct Hcases as [Hlt' | Heq].
  - (* t < t0: transfer from sched to sched' *)
    unfold matches_choose_edf_at_with, matches_dispatch_at_with.
        simpl.
    specialize (Hbefore t Hlt').
    unfold matches_choose_edf_at_with, matches_dispatch_at_with in Hbefore.
    simpl in Hbefore.
    (* sched and sched' agree before t0, so agree before t *)
    assert (Hpre : agrees_before sched sched' t).
    { apply (agrees_before_weaken sched sched' t t0). lia. exact Hagree. }
    assert (Hpre_sym : agrees_before sched' sched t)
      by (exact (agrees_before_sym _ _ _ Hpre)).
    (* sched' t 0 = sched t 0 (agree before t, and t < t0) *)
    assert (Hs't0 : sched' t 0 = sched t 0) by (symmetry; exact (Hagree t 0 Hlt')).
    (* candidates agree due to prefix extensionality *)
    assert (Hcand_eq : candidates_of jobs 1 sched' t = candidates_of jobs 1 sched t).
    { apply (candidates_prefix_extensional J candidates_of cand_spec jobs 1 sched' sched t).
      intros t' c Hlt''.
      destruct (Nat.eq_dec c 0) as [-> | Hcne].
      - symmetry. exact (Hpre t' 0 Hlt'').
      - assert (Hcpos : 0 < c) by lia.
        rewrite (Honly' t' c Hcpos). rewrite (Honly t' c Hcpos). reflexivity. }
    assert (Hchoose_eq : choose_edf jobs 1 sched' t (candidates_of jobs 1 sched' t) =
                         choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)).
    { rewrite Hcand_eq.
      apply (choose_edf_agrees_before jobs sched' sched t (candidates_of jobs 1 sched t)).
      exact Hpre_sym. }
    rewrite Hs't0. rewrite Hchoose_eq. exact Hbefore.
  - subst t. exact Hmatch.
Qed.

(* Strong normalization: produce a schedule that exactly matches choose_edf before H. *)
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
  intros J J_bool candidates_of cand_spec jobs sched H HJbool.
  induction H as [| H' IH].
  - intros Hvalid Hfeas HJonly Hcpu1.
    exists sched.
    refine (conj Hvalid (conj Hfeas (conj HJonly (conj Hcpu1 _)))).
    unfold matches_choose_edf_before, matches_dispatch_before. intros t Hlt. lia.
  - intros Hvalid Hfeas HJonly Hcpu1.
    destruct (IH Hvalid Hfeas HJonly Hcpu1)
        as [sched_ih [Hih_valid [Hih_feas [Hih_Jonly [Hih_cpu1 Hih_canon]]]]].
    (* Decide: is sched_ih canonical at H'? *)
    destruct (is_canonical_at_b candidates_of jobs sched_ih H') eqn:Hb.
    + (* Canonical at H': done *)
      exists sched_ih.
      refine (conj Hih_valid (conj Hih_feas (conj Hih_Jonly (conj Hih_cpu1 _)))).
      unfold matches_choose_edf_before, matches_dispatch_before.
      intros t Hlt.
      assert (Hcases : t < H' \/ t = H') by lia.
      destruct Hcases as [Hlt' | Heq].
      * exact (Hih_canon t Hlt').
      * subst t. apply (is_canonical_at_b_true_iff candidates_of jobs sched_ih H'). exact Hb.
    + (* Not canonical at H': repair *)
      assert (Hnot : ~ matches_choose_edf_at_with jobs candidates_of sched_ih H').
      { apply (is_canonical_at_b_false_iff candidates_of jobs sched_ih H'). exact Hb. }
      destruct (repair_non_canonical_at J J_bool candidates_of cand_spec
                   jobs sched_ih H'
                   HJbool Hih_valid Hih_feas Hih_Jonly Hih_cpu1 Hnot)
          as [sched_r [Hr_valid [Hr_feas [Hr_Jonly [Hr_cpu1 [Hr_agree Hr_match]]]]]].
      exists sched_r.
      refine (conj Hr_valid (conj Hr_feas (conj Hr_Jonly (conj Hr_cpu1 _)))).
      exact (repair_pushes_canonical_forward J candidates_of cand_spec
               jobs sched_ih sched_r H'
               Hih_cpu1 Hr_cpu1 Hr_agree Hr_match Hih_canon).
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
      (* service in trunc = service in orig for times < t *)
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

Lemma trunc_sched_canonical :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H) ->
    matches_choose_edf_before jobs candidates_of sched H ->
    matches_choose_edf_before jobs candidates_of (trunc_sched sched H) H.
Proof.
  intros J candidates_of cand_spec jobs sched H Honly Htrunc_only Hcanon.
  unfold matches_choose_edf_before, matches_dispatch_before, matches_choose_edf_at_with, matches_dispatch_at_with.
  simpl.
  intros t Hlt.
  rewrite (trunc_sched_before sched H t 0 Hlt).
  (* Need: choose_edf jobs 1 (trunc_sched sched H) t (candidates_of ...) =
           choose_edf jobs 1 sched t (candidates_of ...) *)
  assert (Hagree : agrees_before (trunc_sched sched H) sched t).
  { intros t' c Hlt''.
    rewrite (trunc_sched_before sched H t' c (Nat.lt_trans t' t H Hlt'' Hlt)).
    reflexivity. }
  assert (Hagree_sym : agrees_before sched (trunc_sched sched H) t)
    by (exact (agrees_before_sym _ _ _ Hagree)).
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
             (trunc_sched sched H) sched t Hagree).
  rewrite (choose_edf_agrees_before jobs (trunc_sched sched H) sched t _
             Hagree).
  exact (Hcanon t Hlt).
Qed.

(* ===== Section 10: Bridge to scheduler_rel ===== *)

Lemma canonical_and_idle_implies_scheduler_rel :
  forall J enumJ (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_choose_edf_before jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (edf_scheduler candidates_of) jobs 1 sched.
Proof.
  intros J enumJ candidates_of cand_spec jobs sched
         HJ_in Hvalid Hfeas Honly Hcanon Hidle.
  unfold edf_scheduler.
  eapply canonical_and_idle_implies_scheduler_rel_generic; eauto.
Qed.

(* ===== Section 11: Main theorem ===== *)

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
         HJbool HJ_in HJ_complete Hfeas_on.
  (* Step 1: extract feasible witness *)
  destruct Hfeas_on as [sched0 [Hvalid0 Hfeas0]].
  (* Step 2: restrict to CPU 0 only + J-only *)
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
  (* Step 3: strong normalization *)
  set (H := deadline_horizon jobs enumJ).
  destruct (edf_normalize_to_canonical J J_bool candidates_of cand_spec jobs sched1 H
               HJbool Hvalid1 Hfeas1 HJonly1 Hcpu1)
      as [sched2 [Hvalid2 [Hfeas2 [HJonly2 [Hcpu2 Hcanon2]]]]].
  (* Step 4: truncate *)
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
  assert (Hcanon3 : matches_choose_edf_before jobs candidates_of sched3 H).
  { unfold sched3.
    exact (trunc_sched_canonical J candidates_of cand_spec jobs sched2 H
             Hcpu2 (trunc_sched_single_cpu_only sched2 H Hcpu2) Hcanon2). }
  assert (Hidle3 : forall t, H <= t -> sched3 t 0 = None).
  { intros t Hle. unfold sched3.
    exact (trunc_sched_after sched2 H t 0 Hle). }
  (* Step 5: apply bridge *)
  assert (Hrel : scheduler_rel (edf_scheduler candidates_of) jobs 1 sched3).
  { exact (canonical_and_idle_implies_scheduler_rel J enumJ candidates_of cand_spec
             jobs sched3 HJ_in Hvalid3 Hfeas3 Hcpu3 Hcanon3 Hidle3). }
  (* Step 6: apply schedulable_by_on intro *)
  exact (single_cpu_algorithm_schedulable_by_on_intro J edf_generic_spec candidates_of
           cand_spec jobs sched3 Hrel Hfeas3).
Qed.
