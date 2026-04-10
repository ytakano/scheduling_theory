From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import UniPolicies.EDF.
Import ListNotations.

(* ===== Section 1: Service / Completion 補題 ===== *)

(* 区間 [t1, t2) に job j が受けた service 量 *)
Definition service_between
    (m : nat) (sched : Schedule) (j : JobId) (t1 t2 : Time) : nat :=
  service_job m sched j t2 - service_job m sched j t1.

(* 1-1a: completed と service の言い換え *)
Lemma completed_iff_service_ge_cost :
  forall jobs m sched j t,
    completed jobs m sched j t <->
    job_cost (jobs j) <= service_job m sched j t.
Proof.
  intros jobs m sched j t.
  unfold completed. lia.
Qed.

(* 1-1b: not completed と service の言い換え *)
Lemma not_completed_iff_service_lt_cost :
  forall jobs m sched j t,
    ~ completed jobs m sched j t <->
    service_job m sched j t < job_cost (jobs j).
Proof.
  intros jobs m sched j t.
  rewrite completed_iff_service_ge_cost. lia.
Qed.

(* 1-2a: missed_deadline の展開補題 *)
Lemma missed_deadline_iff_not_completed_at_deadline :
  forall jobs m sched j,
    missed_deadline jobs m sched j <->
    ~ completed jobs m sched j (job_abs_deadline (jobs j)).
Proof.
  intros jobs m sched j.
  unfold missed_deadline. tauto.
Qed.

(* 1-2b: missed_deadline を service 比較へ落とす *)
Lemma missed_deadline_iff_service_lt_cost_at_deadline :
  forall jobs m sched j,
    missed_deadline jobs m sched j <->
    service_job m sched j (job_abs_deadline (jobs j)) < job_cost (jobs j).
Proof.
  intros jobs m sched j.
  rewrite missed_deadline_iff_not_completed_at_deadline.
  rewrite not_completed_iff_service_lt_cost.
  tauto.
Qed.

(* 1-3a: service_between の展開 (rewrite 用) *)
Lemma service_between_eq :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_between m sched j t1 t2 =
    service_job m sched j t2 - service_job m sched j t1.
Proof.
  intros m sched j t1 t2 _.
  unfold service_between. reflexivity.
Qed.

(* 1-3b: 左端が 0 のときは service_job そのもの *)
Lemma service_between_0_r :
  forall m sched j t,
    service_between m sched j 0 t = service_job m sched j t.
Proof.
  intros m sched j t.
  unfold service_between. simpl. lia.
Qed.

(* 1-3c: 同じ時刻の区間は 0 *)
Lemma service_between_refl :
  forall m sched j t,
    service_between m sched j t t = 0.
Proof.
  intros m sched j t.
  unfold service_between. lia.
Qed.

(* 1-3d: 区間の分割 *)
Lemma service_between_split :
  forall m sched j t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    service_between m sched j t1 t3 =
    service_between m sched j t1 t2 +
    service_between m sched j t2 t3.
Proof.
  intros m sched j t1 t2 t3 H12 H23.
  unfold service_between.
  pose proof (service_job_monotone m sched j t1 t2 H12) as Hle12.
  pose proof (service_job_monotone m sched j t2 t3 H23) as Hle23.
  lia.
Qed.

(* 1-3e: service_job の単調性を between の形で *)
Lemma service_between_nonneg :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_job m sched j t1 <= service_job m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  exact (service_job_monotone m sched j t1 t2 Hle).
Qed.

(* 1-4a: valid_schedule の下では release 前の service は 0 *)
Lemma service_before_release_zero :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    t <= job_release (jobs j) ->
    service_job m sched j t = 0.
Proof.
  intros jobs m sched j t Hvalid Hle.
  induction t as [| t' IH].
  - simpl. reflexivity.
  - (* S t' <= release ならば t' < release *)
    assert (Ht'lt : t' < job_release (jobs j)) by lia.
    (* service_job の unfold: S t' = cpu_count at t' + service_job t' *)
    rewrite service_job_step.
    (* service_job t' = 0 by IH (t' <= release) *)
    assert (Ht'le : t' <= job_release (jobs j)) by lia.
    rewrite (IH Ht'le).
    (* cpu_count at t' = 0: no CPU runs j at t' (before release) *)
    assert (Hzero : cpu_count m sched j t' = 0).
    { apply (proj2 (cpu_count_zero_iff_not_executed m sched j t')).
      intros c Hclt Hrun.
      (* valid_schedule: running => released *)
      pose proof (valid_no_run_before_release jobs m sched j t' c Hvalid Hclt Hrun) as Hrel.
      (* But t' < release *)
      unfold released in Hrel. lia. }
    lia.
Qed.

(* 1-4b: release 時点での service は 0 (1-4a の corollary) *)
Lemma service_at_release_zero :
  forall jobs m sched j,
    valid_schedule jobs m sched ->
    service_job m sched j (job_release (jobs j)) = 0.
Proof.
  intros jobs m sched j Hvalid.
  apply (service_before_release_zero jobs m sched j (job_release (jobs j))).
  - exact Hvalid.
  - lia.
Qed.

(* ===== Section 2: Prefix agreement 補題 ===== *)

(* 2 つのスケジュールが時刻 t より前のすべての時点・CPU で一致する *)
Definition agrees_before (s1 s2 : Schedule) (t : Time) : Prop :=
  forall t' c, t' < t -> s1 t' c = s2 t' c.

(* 2-0: agrees_before は単調: t1 <= t2 かつ agrees t2 ならば agrees t1 *)
Lemma agrees_before_weaken :
  forall s1 s2 t1 t2,
    t1 <= t2 ->
    agrees_before s1 s2 t2 ->
    agrees_before s1 s2 t1.
Proof.
  intros s1 s2 t1 t2 Hle Hagree t' c Hlt.
  apply Hagree. lia.
Qed.

(* 2-1a: 反射律 *)
Lemma agrees_before_refl :
  forall s t, agrees_before s s t.
Proof.
  intros s t t' c _. reflexivity.
Qed.

(* 2-1b: 対称律 *)
Lemma agrees_before_sym :
  forall s1 s2 t, agrees_before s1 s2 t -> agrees_before s2 s1 t.
Proof.
  intros s1 s2 t Hagree t' c Hlt.
  symmetry. apply Hagree. exact Hlt.
Qed.

(* 2-1c: 推移律 *)
Lemma agrees_before_trans :
  forall s1 s2 s3 t,
    agrees_before s1 s2 t ->
    agrees_before s2 s3 t ->
    agrees_before s1 s3 t.
Proof.
  intros s1 s2 s3 t H12 H23 t' c Hlt.
  rewrite (H12 t' c Hlt). apply H23. exact Hlt.
Qed.

(* 2-2a (helper): 時刻 t での全 CPU が一致すれば cpu_count も一致 *)
Lemma cpu_count_agrees_at :
  forall m s1 s2 j t,
    (forall c, s1 t c = s2 t c) ->
    cpu_count m s1 j t = cpu_count m s2 j t.
Proof.
  induction m as [| m' IH]; intros s1 s2 j t Heq.
  - simpl. reflexivity.
  - simpl.
    unfold runs_on.
    rewrite (Heq m').
    rewrite (IH s1 s2 j t Heq).
    reflexivity.
Qed.

(* 2-2b: agrees_before s1 s2 t ならば service_job も一致 *)
Lemma agrees_before_service_job :
  forall m s1 s2 j t,
    agrees_before s1 s2 t ->
    service_job m s1 j t = service_job m s2 j t.
Proof.
  intros m s1 s2 j t Hagree.
  induction t as [| t' IH].
  - simpl. reflexivity.
  - rewrite (service_job_step m s1 j t').
    rewrite (service_job_step m s2 j t').
    assert (Hcpu : cpu_count m s1 j t' = cpu_count m s2 j t').
    { apply cpu_count_agrees_at.
      intro c. apply Hagree. lia. }
    assert (Hpre : agrees_before s1 s2 t').
    { apply (agrees_before_weaken s1 s2 t' (S t')). lia. exact Hagree. }
    rewrite (IH Hpre). rewrite Hcpu. reflexivity.
Qed.

(* 2-2c: completed の prefix extensionality *)
Lemma agrees_before_completed :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    completed jobs m s1 j t <-> completed jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold completed.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  tauto.
Qed.

(* 2-2d: eligible の prefix extensionality *)
Lemma agrees_before_eligible :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligible jobs m s1 j t <-> eligible jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligible.
  pose proof (agrees_before_completed jobs m s1 s2 j t Hagree) as Hcomp.
  tauto.
Qed.

(* 2-2e: ready の prefix extensionality
   注意: running は s t c を直接参照するため、agrees_before s1 s2 (S t) が必要
   (agrees_before s1 s2 t は strictly before t のみ保証するため不十分) *)
Lemma agrees_before_ready :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 (S t) ->
    ready jobs m s1 j t <-> ready jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  assert (Hpre : agrees_before s1 s2 t)
    by (apply (agrees_before_weaken s1 s2 t (S t)); [lia | exact Hagree]).
  pose proof (agrees_before_eligible jobs m s1 s2 j t Hpre) as Helig.
  assert (Hat : forall c, s1 t c = s2 t c)
    by (intro c; apply Hagree; lia).
  unfold ready.
  split.
  - intros [Hel Hnrun].
    split.
    + exact (proj1 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite (Hat c). exact Hrun.
  - intros [Hel Hnrun].
    split.
    + exact (proj2 Helig Hel).
    + unfold running. intros [c [Hlt Hrun]].
      apply Hnrun. exists c. split. exact Hlt.
      rewrite <- (Hat c). exact Hrun.
Qed.

(* ===== Section 3: Bridge / EDF の prefix 安定性 ===== *)

(* Helper: eligibleb は service_job 経由のみ schedule を参照するため prefix 安定 *)
Lemma eligibleb_agrees_before :
  forall jobs m s1 s2 j t,
    agrees_before s1 s2 t ->
    eligibleb jobs m s1 j t = eligibleb jobs m s2 j t.
Proof.
  intros jobs m s1 s2 j t Hagree.
  unfold eligibleb.
  rewrite (agrees_before_service_job m s1 s2 j t Hagree).
  reflexivity.
Qed.

(* 3-1: candidates_of は prefix で決まる (CandidateSourceSpec.candidates_prefix_extensional のラッパ) *)
Lemma candidates_of_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  destruct cand_spec as [_ _ Hpx].
  exact (Hpx jobs 1 s1 s2 t Hagree).
Qed.

(* 3-2: choose_edf の選択は prefix で決まる *)
Lemma choose_edf_agrees_before :
  forall jobs s1 s2 t candidates,
    agrees_before s1 s2 t ->
    choose_edf jobs 1 s1 t candidates =
    choose_edf jobs 1 s2 t candidates.
Proof.
  intros jobs s1 s2 t candidates Hagree.
  unfold choose_edf.
  f_equal.
  apply List.filter_ext.
  intro j.
  apply eligibleb_agrees_before. exact Hagree.
Qed.

(* 3-3: edf_generic_spec の dispatch は時刻 t の選択が prefix で決まる *)
Lemma edf_dispatch_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    dispatch edf_generic_spec jobs 1 s1 t (candidates_of jobs 1 s1 t) =
    dispatch edf_generic_spec jobs 1 s2 t (candidates_of jobs 1 s2 t).
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  simpl.
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs s1 s2 t Hagree).
  apply choose_edf_agrees_before. exact Hagree.
Qed.

(* ===== Section 4: canonical EDF 一致と EDF priority violation の定義と抽出 ===== *)

(* 4-1: canonical な choose_edf と一致している (候補リスト明示版) *)
Definition matches_choose_edf_at
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  sched t 0 = choose_edf jobs 1 sched t candidates.

(* 4-1b: canonical な choose_edf と一致している (candidates_of 版) *)
Definition matches_choose_edf_at_with
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (t : Time) : Prop :=
  sched t 0 = choose_edf jobs 1 sched t (candidates_of jobs 1 sched t).

(* 4-2: horizon H まで canonical choose_edf に一致する *)
Definition matches_choose_edf_before
    (jobs : JobId -> Job)
    (candidates_of : CandidateSource)
    (sched : Schedule)
    (H : Time) : Prop :=
  forall t, t < H ->
    matches_choose_edf_at_with jobs candidates_of sched t.

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
    apply Hnot. unfold matches_choose_edf_at_with.
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
  unfold matches_choose_edf_at_with in Hmatch.
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

(* ===== Section 6: 交換相手が後ろに存在する補題 ===== *)

(* 6-1: service が区間 [t1, t2) で厳密に増加するなら、実行ステップが存在する *)
Lemma service_increases_implies_executed_in_interval :
  forall m sched j t1 t2,
    t1 < t2 ->
    service_job m sched j t1 < service_job m sched j t2 ->
    exists t',
      t1 <= t' < t2 /\
      0 < cpu_count m sched j t'.
Proof.
  intros m sched j t1 t2 Hlt Hinc.
  induction t2 as [| t2' IH].
  - (* t2 = 0: contradiction with t1 < 0 *)
    lia.
  - (* t2 = S t2' *)
    rewrite service_job_step in Hinc.
    destruct (Nat.eq_dec (cpu_count m sched j t2') 0) as [Hzero | Hpos].
    + (* cpu_count at t2' = 0: service didn't change at last step *)
      rewrite Hzero in Hinc.
      rewrite Nat.add_0_r in Hinc.
      (* So service_job t1 < service_job t2' *)
      assert (Hlt' : t1 < t2').
      { destruct (Nat.eq_dec t1 t2') as [Heq | Hne].
        - subst t2'. lia. (* Hinc : service_job j t1 < service_job j t1, contradiction *)
        - lia. }
      destruct (IH Hlt' Hinc) as [t' [[Hle Hlt''] Hcpu]].
      exists t'. split. split. exact Hle. lia. exact Hcpu.
    + (* cpu_count at t2' > 0: t' = t2' is the witness *)
      exists t2'. split. split. lia. lia. lia.
Qed.

(* 6-2: eligible かつ feasible なら、deadline 前に実行スロットが存在する *)
Lemma eligible_feasible_implies_runs_later_before_deadline :
  forall J jobs sched j t,
    J j ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    eligible jobs 1 sched j t ->
    exists t',
      t <= t' /\
      t' < job_abs_deadline (jobs j) /\
      sched t' 0 = Some j.
Proof.
  intros J jobs sched j t HJj Hvalid Hfeas Helig.
  (* Step 1: eligible → service at t < cost *)
  assert (Hlt_cost : service_job 1 sched j t < job_cost (jobs j)).
  { apply not_completed_iff_service_lt_cost. exact (proj2 Helig). }
  (* Step 2: feasible + J j → service at deadline >= cost (constructive: proof by negation) *)
  assert (Hge_cost : job_cost (jobs j) <= service_job 1 sched j (job_abs_deadline (jobs j))).
  { destruct (le_lt_dec (job_cost (jobs j)) (service_job 1 sched j (job_abs_deadline (jobs j))))
        as [Hge | Hlt_dl].
    - exact Hge.
    - exfalso. apply (Hfeas j HJj). unfold missed_deadline.
      apply not_completed_iff_service_lt_cost. exact Hlt_dl. }
  (* Step 3: service strictly increases from t to deadline *)
  assert (Hinc : service_job 1 sched j t < service_job 1 sched j (job_abs_deadline (jobs j))).
  { lia. }
  (* t < deadline: constructive via lt_dec + service_job_monotone contradiction *)
  assert (Htlt : t < job_abs_deadline (jobs j)).
  { destruct (lt_dec t (job_abs_deadline (jobs j))) as [Hlt | Hnlt].
    - exact Hlt.
    - exfalso.
      assert (Hge : job_abs_deadline (jobs j) <= t) by lia.
      pose proof (service_job_monotone 1 sched j _ _ Hge) as Hmon.
      lia. }
  (* Step 4: extract execution point t' in [t, deadline) *)
  destruct (service_increases_implies_executed_in_interval 1 sched j t (job_abs_deadline (jobs j))
              Htlt Hinc) as [t' [[Hle Hlt'] Hcpu]].
  (* Step 5: cpu_count 1 > 0 → sched t' 0 = Some j *)
  destruct (proj1 (cpu_count_pos_iff_executed 1 sched j t') Hcpu) as [c [Hclt Hrun]].
  assert (Hc0 : c = 0) by lia.
  subst c.
  exists t'. split. exact Hle. split. exact Hlt'. exact Hrun.
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
