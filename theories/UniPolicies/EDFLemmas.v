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

(* ===== Section 4: EDF violation の定義と抽出 ===== *)
(* TODO *)

(* ===== Section 5: 最適性定理への橋渡し補題 ===== *)
(* TODO *)
