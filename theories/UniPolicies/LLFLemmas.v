From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Require Import UniPolicies.MetricChooser.
Require Import UniPolicies.MetricChooserLemmas.
Require Import UniPolicies.LLF.
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
  matches_dispatch_at_with llf_generic_spec jobs candidates_of sched t.

Definition matches_choose_llf_before
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  matches_dispatch_before llf_generic_spec jobs candidates_of sched H.

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
  unfold is_llf_canonical_at_b, matches_choose_llf_at_with, matches_dispatch_at_with.
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

Lemma llf_dispatch_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch llf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch llf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  simpl.
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  apply choose_llf_agrees_before.
  exact Hagree.
Qed.
