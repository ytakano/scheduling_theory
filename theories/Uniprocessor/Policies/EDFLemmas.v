From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Uniprocessor.Generic.SchedulingAlgorithmCanonicalBridge.
From SchedulingTheory Require Import Abstractions.Scheduler.Validity.
From SchedulingTheory Require Import Refinement.SchedulingAlgorithmRefinement.
From SchedulingTheory Require Import Uniprocessor.Policies.Common.MetricChooser.
From SchedulingTheory Require Import Uniprocessor.Policies.Common.MetricChooserLemmas.
From SchedulingTheory Require Import Uniprocessor.Policies.EDF.
Import ListNotations.

(* ===== Section 3: Bridge / EDF の prefix 安定性 ===== *)

Lemma choose_edf_agrees_before :
  forall jobs s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_edf jobs 1 s1 t candidates =
    choose_edf jobs 1 s2 t candidates.
Proof.
  intros jobs s1 s2 t candidates Hagree.
  unfold choose_edf.
  apply choose_min_metric_agrees_before. exact Hagree.
Qed.

Lemma edf_choose_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    choose edf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    choose edf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  simpl.
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  apply choose_edf_agrees_before. exact Hagree.
Qed.

(* ===== Section 4: canonical EDF 一致と EDF priority violation の定義と抽出 ===== *)

Definition matches_choose_edf_at
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  sched t 0 = choose_edf jobs 1 sched t candidates.

Definition matches_choose_edf_at_with
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  matches_choose_at_with edf_generic_spec jobs candidates_of sched t.

Definition matches_choose_edf_before
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  matches_choose_before edf_generic_spec jobs candidates_of sched H.

(* 4-3: EDF の本質的な priority 性質 (J なし版) *)
Definition respects_edf_priority_at
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  forall j j',
    sched t 0 = Some j ->
    eligible jobs 1 sched j' t ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    False.

(* 4-3b: EDF の本質的な priority 性質 (J あり版) *)
Definition respects_edf_priority_at_on
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  forall j j',
    J j ->
    J j' ->
    sched t 0 = Some j ->
    eligible jobs 1 sched j' t ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    False.

(* 4-4: EDF violation at t — strict に早い deadline の eligible job を無視している *)
Definition edf_violation_at
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  exists j j',
    sched t 0 = Some j /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).

(* 4-5: canonical 不一致なら「別の min-or-better eligible job」がいる *)
Lemma canonical_non_edf_step_has_other_min_or_better_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    ~ matches_choose_edf_at_with jobs candidates_of sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) /\
      j' <> j.
Proof.
  intros J candidates_of cand_spec jobs sched t j Hvalid Hsched HJj Hnot.
  (* Step 1: eligible jobs 1 sched j t from valid_schedule *)
  assert (Helig_j : eligible jobs 1 sched j t).
  { apply (valid_running_implies_eligible jobs 1 sched j t 0).
    - exact Hvalid.
    - lia.
    - exact Hsched. }
  (* Step 2: In j (candidates_of ...) from candidates_complete *)
  assert (Hin_j : In j (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j HJj Helig_j). }
  (* Step 3: choose_edf returns Some j' *)
  destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t))
      as [j' Hchoose].
  { exists j. split. exact Hin_j. exact Helig_j. }
  (* Step 4: properties of j' *)
  assert (Hj'_in : In j' (candidates_of jobs 1 sched t)).
  { exact (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose). }
  assert (Hj'_elig : eligible jobs 1 sched j' t).
  { exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose). }
  assert (Hj'_le : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
  { exact (choose_edf_min_deadline jobs 1 sched t _ j' Hchoose j Hin_j Helig_j). }
  (* Step 5: j' <> j from ~ matches_choose_edf_at_with *)
  assert (Hneq : j' <> j).
  { intro Heq. subst j'.
    apply Hnot. unfold matches_choose_edf_at_with, matches_choose_at_with.
    rewrite Hsched. symmetry. exact Hchoose. }
  exists j'.
  split. exact Hj'_in.
  split. exact Hj'_elig.
  split. exact Hj'_le.
  exact Hneq.
Qed.

(* ===== Section 5: 最適性定理への橋渡し補題 ===== *)

(* 5-1: EDF violation は earlier-deadline eligible job の存在を露出する *)
Lemma edf_violation_exposes_exchange_pair :
  forall jobs sched t j,
    sched t 0 = Some j ->
    edf_violation_at jobs sched t ->
    exists j',
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
Proof.
  intros jobs sched t j Hsched Hviol.
  unfold edf_violation_at in Hviol.
  destruct Hviol as [j_run [j' [Hrun [Helig Hlt]]]].
  rewrite Hsched in Hrun.
  injection Hrun as Heq. subst j_run.
  exists j'.
  split. exact Helig. exact Hlt.
Qed.

(* 5-2: canonical EDF step では J 内に strict earlier-deadline eligible job は存在しない *)
Lemma matches_choose_edf_at_with_no_earlier_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    sched t 0 = Some j ->
    forall j',
      J j' ->
      eligible jobs 1 sched j' t ->
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
      False.
Proof.
  intros J candidates_of cand_spec jobs sched t j Hmatch Hsched j' HJj' Helig Hlt.
  unfold matches_choose_edf_at_with, matches_choose_at_with in Hmatch.
  rewrite Hsched in Hmatch.
  assert (Hchoose : choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j).
  { symmetry. exact Hmatch. }
  assert (Hin : In j' (candidates_of jobs 1 sched t)).
  { destruct cand_spec as [_ Hcomplete _].
    exact (Hcomplete jobs 1 sched t j' HJj' Helig). }
  pose proof (choose_edf_min_deadline jobs 1 sched t _ j Hchoose j' Hin Helig) as Hle.
  lia.
Qed.

(* 5-3: canonical 一致は respects_edf_priority_at_on を含意する *)
Lemma matches_choose_edf_at_with_implies_respects_edf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    respects_edf_priority_at_on J jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hmatch.
  unfold respects_edf_priority_at_on.
  intros j j' _ HJj' Hsched Helig Hlt.
  exact (matches_choose_edf_at_with_no_earlier_eligible_job
           J candidates_of cand_spec jobs sched t j Hmatch Hsched j' HJj' Helig Hlt).
Qed.

(* ===== Section 7: 有限 violation 述語 ===== *)

(* 7-1: explicit candidates list 版 violation 定義 *)
Definition edf_violation_at_in
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (cands : list JobId) : Prop :=
  exists j j',
    J j /\
    J j' /\
    sched t 0 = Some j /\
    In j' cands /\
    eligible jobs 1 sched j' t /\
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).

(* 7-2: candidates_of 版 violation 定義 *)
Definition edf_violation_at_with
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  edf_violation_at_in J jobs sched t (candidates_of jobs 1 sched t).

(* 7-3: canonical EDF step では finite violation がない *)
Lemma matches_choose_edf_at_with_no_finite_violation :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    ~ edf_violation_at_with J candidates_of jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hmatch Hviol.
  unfold edf_violation_at_with, edf_violation_at_in in Hviol.
  destruct Hviol as [j [j' [_HJj [HJj' [Hsched [_Hin [Helig Hlt]]]]]]].
  exact (matches_choose_edf_at_with_no_earlier_eligible_job
           J candidates_of cand_spec jobs sched t j Hmatch Hsched j' HJj' Helig Hlt).
Qed.

(* ===== Section 8: Boolean 判定器 ===== *)

(* 8-1: Boolean violation 判定器 (explicit candidates 版) *)
Definition edf_violationb_in
    (J_bool : JobId -> bool)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (cands : list JobId) : bool :=
  match sched t 0 with
  | None => false
  | Some j =>
    J_bool j &&
    existsb (fun j' =>
      J_bool j' &&
      eligibleb jobs 1 sched j' t &&
      Nat.ltb (job_abs_deadline (jobs j')) (job_abs_deadline (jobs j)))
    cands
  end.

(* 8-2: Boolean violation 判定器 (candidates_of 版) *)
Definition edf_violationb_at_with
    (J_bool : JobId -> bool)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : bool :=
  edf_violationb_in J_bool jobs sched t (candidates_of jobs 1 sched t).

(* 8-3: Boolean / Prop 対応 *)
Lemma edf_violationb_in_true_iff :
  forall (J_bool : JobId -> bool) (J : JobId -> Prop)
         (jobs : JobId -> Job)
         (sched : Schedule)
         (t : Time)
         (cands : list JobId),
    (forall j, J_bool j = true <-> J j) ->
    edf_violationb_in J_bool jobs sched t cands = true <->
    edf_violation_at_in J jobs sched t cands.
Proof.
  intros J_bool J jobs sched t cands HJ_bool.
  unfold edf_violationb_in, edf_violation_at_in.
  split.
  - intro Hb.
    destruct (sched t 0) as [j|] eqn:Hsched.
    2: discriminate.
    apply andb_true_iff in Hb as [HJjb Hexistsb].
    apply existsb_exists in Hexistsb as [j' [Hin Hcond]].
    apply andb_true_iff in Hcond as [Hcond' Hltb].
    apply andb_true_iff in Hcond' as [HJj'b Heligb].
    apply Nat.ltb_lt in Hltb.
    apply eligibleb_iff in Heligb.
    apply (proj1 (HJ_bool j)) in HJjb.
    apply (proj1 (HJ_bool j')) in HJj'b.
    exists j, j'.
    split. exact HJjb.
    split. exact HJj'b.
    split. reflexivity.
    split. exact Hin.
    split. exact Heligb.
    exact Hltb.
  - intro Hviol.
    destruct Hviol as [j [j' [HJj [HJj' [Hsched [Hin [Helig Hlt]]]]]]].
    rewrite Hsched.
    apply andb_true_iff. split.
    + apply (proj2 (HJ_bool j)). exact HJj.
    + apply existsb_exists.
      exists j'. split. exact Hin.
      apply andb_true_iff. split.
      * apply andb_true_iff. split.
        -- apply (proj2 (HJ_bool j')). exact HJj'.
        -- apply eligibleb_iff. exact Helig.
      * apply Nat.ltb_lt. exact Hlt.
Qed.

(* 8-4: at_with 版のコロラリ *)
Lemma edf_violationb_at_with_true_iff :
  forall (J_bool : JobId -> bool) (J : JobId -> Prop)
         (candidates_of : CandidateSource)
         (jobs : JobId -> Job)
         (sched : Schedule)
         (t : Time),
    (forall j, J_bool j = true <-> J j) ->
    edf_violationb_at_with J_bool candidates_of jobs sched t = true <->
    edf_violation_at_with J candidates_of jobs sched t.
Proof.
  intros J_bool J candidates_of jobs sched t HJ_bool.
  unfold edf_violationb_at_with, edf_violation_at_with.
  apply edf_violationb_in_true_iff. exact HJ_bool.
Qed.

(* ===== Section 9: Constructive first violation ===== *)

(* 9-1: 有限探索補助関数 (base から base+n-1 を線形探索) *)
Fixpoint find_first_in_range (p : nat -> bool) (base n : nat) : option nat :=
  match n with
  | 0 => None
  | S n' =>
    if p base then Some base
    else find_first_in_range p (S base) n'
  end.

(* 9-2: find_first_in_range Some 仕様 *)
Lemma find_first_in_range_some_spec :
  forall n p base t0,
    find_first_in_range p base n = Some t0 ->
    base <= t0 < base + n /\
    p t0 = true /\
    (forall t, base <= t -> t < t0 -> p t = false).
Proof.
  induction n as [|n' IH]; intros p base t0 H.
  - simpl in H. discriminate.
  - cbn in H.
    destruct (p base) eqn:Hpbase.
    + injection H as Heq.
      rewrite <- Heq.
      split. split; lia.
      split. exact Hpbase.
      intros t Hle Hlt. lia.
    + specialize (IH p (S base) t0 H) as [[Hlo Hhi] [Hpt0 Hmin]].
      split. split; lia.
      split. exact Hpt0.
      intros t Hle Hlt.
      destruct (Nat.eq_dec t base) as [Heq | Hne].
      * subst. exact Hpbase.
      * apply Hmin. lia. exact Hlt.
Qed.

(* 9-3: find_first_in_range None 仕様 *)
Lemma find_first_in_range_none_spec :
  forall n p base,
    find_first_in_range p base n = None ->
    forall t, base <= t -> t < base + n -> p t = false.
Proof.
  induction n as [|n' IH]; intros p base H t Hle Hlt.
  - lia.
  - cbn in H.
    destruct (p base) eqn:Hpbase.
    + discriminate.
    + destruct (Nat.eq_dec t base) as [Heq | Hne].
      * subst. exact Hpbase.
      * apply (IH p (S base) H). lia. lia.
Qed.

(* 9-4: first_nat_up_to 定義 *)
Definition first_nat_up_to (H : nat) (p : nat -> bool) : option nat :=
  find_first_in_range p 0 H.

(* 9-5: first_nat_up_to Some 仕様 *)
Lemma first_nat_up_to_some_spec :
  forall H p t0,
    first_nat_up_to H p = Some t0 ->
    t0 < H /\ p t0 = true /\ (forall t, t < t0 -> p t = false).
Proof.
  intros H p t0 Hfirst.
  unfold first_nat_up_to in Hfirst.
  apply find_first_in_range_some_spec in Hfirst.
  destruct Hfirst as [[_Hbase Htop] [Hpt0 Hmin]].
  split. lia.
  split. exact Hpt0.
  intros t Hlt. apply Hmin. lia. exact Hlt.
Qed.

(* 9-6: first_nat_up_to None 仕様 *)
Lemma first_nat_up_to_none_spec :
  forall H p,
    first_nat_up_to H p = None ->
    forall t, t < H -> p t = false.
Proof.
  intros H p Hnone t Hlt.
  unfold first_nat_up_to in Hnone.
  exact (find_first_in_range_none_spec H p 0 Hnone t (Nat.le_0_l t) Hlt).
Qed.

(* 9-7: constructive first EDF violation 抽出 (classic 不要) *)
Lemma exists_first_edf_violation_before_with :
  forall J (J_bool : JobId -> bool)
         (candidates_of : CandidateSource)
         (jobs : JobId -> Job)
         (sched : Schedule)
         (H : nat),
    (forall j, J_bool j = true <-> J j) ->
    (exists t, t < H /\ edf_violation_at_with J candidates_of jobs sched t) ->
    exists t0,
      t0 < H /\
      edf_violation_at_with J candidates_of jobs sched t0 /\
      (forall t, t < t0 -> ~ edf_violation_at_with J candidates_of jobs sched t).
Proof.
  intros J J_bool candidates_of jobs sched H HJ_bool [t [HtH Hviol]].
  (* Convert violation to boolean *)
  assert (Hviol_b : edf_violationb_at_with J_bool candidates_of jobs sched t = true).
  { apply (edf_violationb_at_with_true_iff J_bool J candidates_of jobs sched t HJ_bool).
    exact Hviol. }
  (* Compute first violation time *)
  destruct (first_nat_up_to H (edf_violationb_at_with J_bool candidates_of jobs sched))
      as [t0|] eqn:Hopt.
  - apply first_nat_up_to_some_spec in Hopt.
    destruct Hopt as [Ht0H [Ht0b Hmin]].
    exists t0.
    split. exact Ht0H.
    split.
    + apply (edf_violationb_at_with_true_iff J_bool J candidates_of jobs sched t0 HJ_bool).
      exact Ht0b.
    + intros t' Hlt' Hviol'.
      assert (Hb' : edf_violationb_at_with J_bool candidates_of jobs sched t' = true).
      { apply (edf_violationb_at_with_true_iff J_bool J candidates_of jobs sched t' HJ_bool).
        exact Hviol'. }
      rewrite (Hmin t' Hlt') in Hb'. discriminate.
  - (* None: contradicts existence of t with violation *)
    exfalso.
    pose proof (first_nat_up_to_none_spec H _ Hopt t HtH) as Hcontra.
    rewrite Hcontra in Hviol_b. discriminate.
Qed.

(* ===== Section 10: Compatibility layer for edf_policy ===== *)

(* 10-1: canonical EDF match implies respects_algorithm_spec_at_with edf_policy.
   Bridge from the old matches_choose_edf_at_with API to the new policy layer. *)
Lemma matches_choose_edf_at_with_implies_respects_edf_policy_at_with :
  forall jobs candidates_of sched t,
    matches_choose_edf_at_with jobs candidates_of sched t ->
    respects_algorithm_spec_at_with edf_policy jobs candidates_of sched t.
Proof.
  intros jobs candidates_of sched t Hmatch.
  unfold matches_choose_edf_at_with, matches_choose_at_with in Hmatch.
  unfold respects_algorithm_spec_at_with.
  rewrite Hmatch.
  exact (choose_edf_refines_edf_policy jobs 1 sched t (candidates_of jobs 1 sched t)).
Qed.

(* 10-2: respects_algorithm_spec_at_with edf_policy implies respects_edf_priority_at_on.
   Extracts the EDF priority invariant from the abstract policy view. *)
Lemma respects_edf_policy_at_with_implies_respects_edf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    respects_algorithm_spec_at_with edf_policy jobs candidates_of sched t ->
    respects_edf_priority_at_on J jobs sched t.
Proof.
  intros J candidates_of cand_spec jobs sched t Hresp.
  unfold respects_edf_priority_at_on.
  intros j j' _ HJj' Hsched Helig Hlt.
  unfold respects_algorithm_spec_at_with in Hresp.
  rewrite Hsched in Hresp.
  unfold edf_policy in Hresp.
  destruct Hresp as [_ [_ Hmin]].
  destruct cand_spec as [_ Hcomplete _].
  assert (Hin : In j' (candidates_of jobs 1 sched t)).
  { exact (Hcomplete jobs 1 sched t j' HJj' Helig). }
  pose proof (Hmin j' Hin Helig) as Hle.
  lia.
Qed.
