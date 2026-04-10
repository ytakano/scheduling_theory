From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
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

(* ===== Section 2: Interval execution lemmas ===== *)

(* 2-1: service が区間 [t1, t2) で厳密に増加するなら、実行ステップが存在する *)
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

(* 2-2: eligible かつ feasible なら、deadline 前に実行スロットが存在する *)
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
