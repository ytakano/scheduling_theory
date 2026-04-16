From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.SchedulingAlgorithmCanonicalBridge.
From RocqSched Require Import Abstractions.Scheduler.Validity.
From RocqSched Require Import Refinement.SchedulingAlgorithmRefinement.
From RocqSched Require Import Uniprocessor.Policies.Common.MetricChooser.
From RocqSched Require Import Uniprocessor.Policies.Common.MetricChooserLemmas.
From RocqSched Require Import Uniprocessor.Policies.LLF.
Import ListNotations.

Definition matches_choose_llf_at
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  sched t 0 = choose_llf jobs 1 sched t candidates.

Definition matches_choose_llf_at_with
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  matches_choose_at_with llf_generic_spec jobs candidates_of sched t.

Definition matches_choose_llf_before
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  matches_choose_before llf_generic_spec jobs candidates_of sched H.

Definition is_llf_canonical_at_b
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : bool :=
  match sched t 0, choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) with
  | None, None => true
  | Some j, Some j' => Nat.eqb j j'
  | _, _ => false
  end.

Lemma is_llf_canonical_at_b_true_iff :
  forall candidates_of jobs sched t,
    is_llf_canonical_at_b candidates_of jobs sched t = true <->
    matches_choose_llf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  unfold is_llf_canonical_at_b, matches_choose_llf_at_with, matches_choose_at_with.
  simpl.
  destruct (sched t 0) as [j|] eqn:Es;
  destruct (choose_llf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Ec.
  - split.
    + intro H. apply Nat.eqb_eq in H. subst j'. reflexivity.
    + intro H. injection H as Heq. apply Nat.eqb_eq. exact Heq.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; reflexivity.
Qed.

Lemma is_llf_canonical_at_b_false_iff :
  forall candidates_of jobs sched t,
    is_llf_canonical_at_b candidates_of jobs sched t = false <->
    ~ matches_choose_llf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  rewrite <- is_llf_canonical_at_b_true_iff.
  destruct (is_llf_canonical_at_b candidates_of jobs sched t).
  - split; intro H; [discriminate | exact (False_ind _ (H eq_refl))].
  - split; intro H; [intro Hf; discriminate | reflexivity].
Qed.

Lemma choose_llf_agrees_before :
  forall jobs s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_llf jobs 1 s1 t candidates =
    choose_llf jobs 1 s2 t candidates.
Proof.
  intros jobs s1 s2 t candidates Hagree.
  unfold choose_llf, choose_min_metric.
  assert (Hfilter :
    filter (fun j : JobId => eligibleb jobs 1 s1 j t) candidates =
    filter (fun j : JobId => eligibleb jobs 1 s2 j t) candidates).
  {
    apply List.filter_ext.
    intro j.
    apply eligibleb_agrees_before.
    exact Hagree.
  }
  rewrite Hfilter.
  apply min_metric_job_ext.
  intros j Hin.
  unfold llf_metric.
  apply agrees_before_laxity.
  exact Hagree.
Qed.

Lemma choose_llf_filter_ineligible :
  forall jobs sched t candidates keep,
    (forall j, In j candidates -> keep j = false -> ~ eligible jobs 1 sched j t) ->
    choose_llf jobs 1 sched t candidates =
    choose_llf jobs 1 sched t (filter keep candidates).
Proof.
  intros jobs sched t candidates keep Hnone.
  unfold choose_llf, choose_min_metric.
  f_equal.
  induction candidates as [|j candidates IH]; simpl.
  - reflexivity.
  - destruct (eligibleb jobs 1 sched j t) eqn:Helig,
             (keep j) eqn:Hkeep; simpl.
    + rewrite Helig.
      rewrite IH.
      * reflexivity.
      * intros j' Hin Hk.
        apply Hnone.
        right; exact Hin.
        exact Hk.
    + exfalso.
      apply (Hnone j (or_introl eq_refl) Hkeep).
      apply eligibleb_iff.
      exact Helig.
    + rewrite Helig.
      rewrite IH.
      * reflexivity.
      * intros j' Hin Hk.
        apply Hnone.
        right; exact Hin.
        exact Hk.
    + rewrite IH.
      * reflexivity.
      * intros j' Hin Hk.
        apply Hnone.
        right; exact Hin.
        exact Hk.
Qed.

Lemma llf_choose_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    choose llf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    choose llf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  simpl.
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  apply choose_llf_agrees_before.
  exact Hagree.
Qed.

(* ===== Section 4: canonical LLF 一致と LLF priority violation の定義と抽出 ===== *)

Definition respects_llf_priority_at_on
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  forall j j',
    sched t 0 = Some j ->
    J j ->
    J j' ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j t <= laxity jobs 1 sched j' t)%Z.

Definition llf_violation_at_in
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  exists j j',
    sched t 0 = Some j /\
    J j /\
    In j' candidates /\
    J j' /\
    eligible jobs 1 sched j' t /\
    (laxity jobs 1 sched j' t < laxity jobs 1 sched j t)%Z.

Definition llf_violation_at_with
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  llf_violation_at_in J jobs sched t (candidates_of jobs 1 sched t).

Lemma matches_choose_llf_at_with_no_lower_laxity_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j j',
    matches_choose_llf_at_with jobs candidates_of sched t ->
    sched t 0 = Some j ->
    In j' (candidates_of jobs 1 sched t) ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j t <= laxity jobs 1 sched j' t)%Z.
Proof.
  intros J candidates_of cand_spec jobs sched t j j' Hmatch Hsched Hin Helig.
  unfold matches_choose_llf_at_with, matches_choose_at_with in Hmatch.
  rewrite Hsched in Hmatch.
  assert (Hchoose : choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j).
  { symmetry. exact Hmatch. }
  exact (choose_llf_min_laxity jobs 1 sched t _ j Hchoose j' Hin Helig).
Qed.

Lemma matches_choose_llf_at_with_implies_respects_llf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_llf_at_with jobs candidates_of sched t ->
    respects_llf_priority_at_on J jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hmatch.
  unfold respects_llf_priority_at_on.
  intros j j' Hsched HJj HJj' Helig.
  assert (Hin : In j' (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j' HJj' Helig). }
  exact (matches_choose_llf_at_with_no_lower_laxity_eligible_job
           J candidates_of cand_spec jobs sched t j j' Hmatch Hsched Hin Helig).
Qed.

Lemma matches_choose_llf_at_with_no_finite_violation :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_llf_at_with jobs candidates_of sched t ->
    ~ llf_violation_at_with J candidates_of jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hmatch Hviol.
  unfold llf_violation_at_with, llf_violation_at_in in Hviol.
  destruct Hviol as [j [j' [Hsched [_HJj [Hin [_HJj' [Helig Hlt]]]]]]].
  pose proof
    (matches_choose_llf_at_with_no_lower_laxity_eligible_job
       J candidates_of cand_spec jobs sched t j j' Hmatch Hsched Hin Helig) as Hle.
  lia.
Qed.

Lemma canonical_non_llf_step_has_other_min_or_better_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    ~ matches_choose_llf_at_with jobs candidates_of sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z /\
      j' <> j /\
      choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.
Proof.
  intros J candidates_of cand_spec jobs sched t j Hvalid Hsched HJj Hnot.
  assert (Helig_j : eligible jobs 1 sched j t).
  { apply (valid_running_implies_eligible jobs 1 sched j t 0).
    - exact Hvalid.
    - lia.
    - exact Hsched. }
  assert (Hin_j : In j (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j HJj Helig_j). }
  destruct (choose_llf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t))
    as [j' Hchoose].
  { exists j. split. exact Hin_j. exact Helig_j. }
  assert (Hin_j' : In j' (candidates_of jobs 1 sched t)).
  { exact (choose_llf_in_candidates jobs 1 sched t _ j' Hchoose). }
  assert (Helig_j' : eligible jobs 1 sched j' t).
  { exact (choose_llf_eligible jobs 1 sched t _ j' Hchoose). }
  assert (Hle : (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z).
  { exact (choose_llf_min_laxity jobs 1 sched t _ j' Hchoose j Hin_j Helig_j). }
  assert (Hneq : j' <> j).
  { intro Heq. subst j'.
    apply Hnot.
    unfold matches_choose_llf_at_with, matches_choose_at_with.
    rewrite Hsched. symmetry. exact Hchoose. }
  exists j'.
  split. exact Hin_j'.
  split. exact Helig_j'.
  split. exact Hle.
  split. exact Hneq.
  exact Hchoose.
Qed.
