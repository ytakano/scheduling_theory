From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
Require Import Base.
Require Import ScheduleModel.
Import ListNotations.


(* ===== Lemmas from ScheduleModel.v ===== *)

(* ===== Lv.0 Lemmas ===== *)

(* --- runs_on helpers --- *)

Lemma runs_on_true_iff : forall sched j t c,
    runs_on sched j t c = true <-> sched t c = Some j.
Proof.
  intros. unfold runs_on.
  destruct (sched t c) as [j'|].
  - split.
    + intro H. apply Nat.eqb_eq in H. subst. reflexivity.
    + intro H. injection H as Heq. subst. apply Nat.eqb_refl.
  - split; discriminate.
Qed.

Lemma runs_on_false_iff : forall sched j t c,
    runs_on sched j t c = false <-> sched t c <> Some j.
Proof.
  intros. unfold runs_on.
  destruct (sched t c) as [j'|].
  - split.
    + intro H. apply Nat.eqb_neq in H.
      intro Heq. injection Heq as Heq'. subst. exact (H eq_refl).
    + intro H. apply Nat.eqb_neq.
      intro Heq. subst. exact (H eq_refl).
  - split.
    + intros _. discriminate.
    + intros _. reflexivity.
Qed.

(* --- service_job lemmas --- *)

(* Matches the Fixpoint definition order exactly *)
Lemma service_job_unfold : forall m sched j t,
    service_job m sched j (S t) = cpu_count m sched j t + service_job m sched j t.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Commuted form; use this for rewriting when the sum order matters *)
Lemma service_job_step : forall m sched j t,
    service_job m sched j (S t) = service_job m sched j t + cpu_count m sched j t.
Proof.
  intros. rewrite service_job_unfold. lia.
Qed.

(* --- cpu_count characterization lemmas --- *)

Lemma cpu_count_zero_iff_not_executed : forall m sched j t,
    cpu_count m sched j t = 0 <->
    forall c, c < m -> sched t c <> Some j.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - split; [intros _ c Hlt; lia | intros; reflexivity].
  - split.
    + intros Hzero c Hlt.
      simpl in Hzero.
      destruct (runs_on sched j t m') eqn:Erun.
      * (* runs_on = true: 1 + ... = 0, contradiction *)
        simpl in Hzero. lia.
      * (* runs_on = false: 0 + cpu_count m' = 0 *)
        simpl in Hzero.
        apply Nat.lt_succ_r in Hlt.
        destruct (Nat.eq_dec c m') as [-> | Hne].
        -- exact (proj1 (runs_on_false_iff sched j t m') Erun).
        -- apply (proj1 (IH sched j t) Hzero). lia.
    + intros Hnone.
      simpl.
      destruct (runs_on sched j t m') eqn:Erun.
      * (* runs_on = true: m' runs j, contradicts Hnone *)
        apply runs_on_true_iff in Erun.
        exfalso. exact (Hnone m' (Nat.lt_succ_diag_r m') Erun).
      * simpl.
        apply (proj2 (IH sched j t)).
        intros c Hlt. apply Hnone. lia.
Qed.

(* Boolean version of ready: needed for filter (requires bool-valued function).
   readyb_iff proves readyb j t = true <-> ready j t.
   Shared by all dispatch policies (EDF, FIFO, RR, …).
   Placed here because readyb_iff uses cpu_count_zero_iff_not_executed. *)
Definition readyb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                   (j : JobId) (t : Time) : bool :=
  (job_release (jobs j) <=? t) &&
  negb (job_cost (jobs j) <=? service_job m sched j t) &&
  (cpu_count m sched j t =? 0).

Lemma readyb_iff : forall jobs m sched j t,
    readyb jobs m sched j t = true <-> ready jobs m sched j t.
Proof.
  intros jobs m sched j t.
  unfold readyb, ready, eligible, running, released, completed.
  rewrite Bool.andb_true_iff, Bool.andb_true_iff, Nat.leb_le,
          Bool.negb_true_iff, Nat.eqb_eq.
  split.
  - intros [[H1 H2] H3]. split.
    + split.
      * exact H1.
      * intro Hge. apply Nat.leb_le in Hge. rewrite Hge in H2. discriminate.
    + intros [c [Hlt Hc]].
      apply (proj1 (cpu_count_zero_iff_not_executed m sched j t) H3 c Hlt).
      exact Hc.
  - intros [[H1 H2] H3]. split; [split|].
    + exact H1.
    + apply Bool.not_true_iff_false. intro H. apply Nat.leb_le in H. exact (H2 H).
    + apply (proj2 (cpu_count_zero_iff_not_executed m sched j t)).
      intros c Hlt Hc. apply H3. exists c. split. exact Hlt. exact Hc.
Qed.

(* Boolean version of eligible: like readyb but without the cpu_count = 0 check.
   Needed for dispatch policies that select from eligible (not necessarily idle) jobs.
   eligibleb_iff proves eligibleb j t = true <-> eligible j t. *)
Definition eligibleb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                     (j : JobId) (t : Time) : bool :=
  (job_release (jobs j) <=? t) &&
  negb (job_cost (jobs j) <=? service_job m sched j t).

Lemma eligibleb_iff : forall jobs m sched j t,
    eligibleb jobs m sched j t = true <-> eligible jobs m sched j t.
Proof.
  intros jobs m sched j t.
  unfold eligibleb, eligible, released, completed.
  rewrite Bool.andb_true_iff, Nat.leb_le, Bool.negb_true_iff.
  split.
  - intros [H1 H2]. split.
    + exact H1.
    + intro Hge. apply Nat.leb_le in Hge. rewrite Hge in H2. discriminate.
  - intros [H1 H2]. split.
    + exact H1.
    + apply Bool.not_true_iff_false. intro H. apply Nat.leb_le in H. exact (H2 H).
Qed.

Lemma cpu_count_pos_iff_executed : forall m sched j t,
    0 < cpu_count m sched j t <->
    exists c, c < m /\ sched t c = Some j.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - simpl. split.
    + intro H. lia.
    + intros [c [Hlt _]]. lia.
  - split.
    + intros Hpos.
      simpl in Hpos.
      destruct (runs_on sched j t m') eqn:Erun.
      * apply runs_on_true_iff in Erun.
        exists m'. split. lia. exact Erun.
      * simpl in Hpos.
        destruct (proj1 (IH sched j t) Hpos) as [c' [Hlt' Hrun']].
        exists c'. split. lia. exact Hrun'.
    + intros [c [Hlt Hrun]].
      simpl.
      apply Nat.lt_succ_r in Hlt.
      destruct (Nat.eq_dec c m') as [-> | Hne].
      * (* c = m': runs_on = true *)
        assert (Hruns : runs_on sched j t m' = true).
        { apply runs_on_true_iff. exact Hrun. }
        rewrite Hruns. simpl. lia.
      * (* c < m': use IH *)
        assert (Hlt' : c < m') by lia.
        assert (Hpos : 0 < cpu_count m' sched j t).
        { apply (proj2 (IH sched j t)). exists c. split. exact Hlt'. exact Hrun. }
        destruct (runs_on sched j t m'); simpl; lia.
Qed.

(* Equivalent to cpu_count_pos_iff_executed; useful when lia cannot close goals
   involving strict positivity, e.g. when rewriting with Nat.neq_0_lt_0. *)
Lemma cpu_count_nonzero_iff_executed : forall m sched j t,
    cpu_count m sched j t <> 0 <->
    exists c, c < m /\ sched t c = Some j.
Proof.
  intros m sched j t.
  split.
  - intros Hnz. apply cpu_count_pos_iff_executed. lia.
  - intros Hex.
    pose proof (proj2 (cpu_count_pos_iff_executed m sched j t) Hex) as Hpos.
    lia.
Qed.

(* Under sequential_jobs, cpu_count <= 1 *)
Lemma cpu_count_le_1 : forall m sched j t,
    sequential_jobs m sched ->
    cpu_count m sched j t <= 1.
Proof.
  induction m as [| m' IH]; intros sched j t Hnd.
  - simpl. lia.
  - simpl.
    destruct (runs_on sched j t m') eqn:Erun.
    + (* runs_on = true: cpu_count m' must be 0 *)
      apply runs_on_true_iff in Erun.
      simpl.
      assert (Hzero : cpu_count m' sched j t = 0).
      { apply (proj2 (cpu_count_zero_iff_not_executed m' sched j t)).
        intros c Hlt Hrun.
        assert (Heq : c = m').
        { apply (Hnd j t c m').
          - lia.
          - lia.
          - exact Hrun.
          - exact Erun. }
        lia. }
      lia.
    + (* runs_on = false *)
      simpl.
      assert (Hnd' : sequential_jobs m' sched).
      { intros j0 t0 c1 c2 H1 H2 H3 H4.
        apply (Hnd j0 t0 c1 c2).
        - lia.
        - lia.
        - exact H3.
        - exact H4. }
      exact (IH sched j t Hnd').
Qed.

(* Stronger form: cpu_count is exactly 0 or 1 under sequential_jobs *)
Lemma cpu_count_0_or_1 : forall m sched j t,
    sequential_jobs m sched ->
    cpu_count m sched j t = 0 \/ cpu_count m sched j t = 1.
Proof.
  intros m sched j t Hnd.
  pose proof (cpu_count_le_1 m sched j t Hnd) as Hle.
  destruct (cpu_count m sched j t) as [| n].
  - left. reflexivity.
  - right. lia.
Qed.

(* Under sequential_jobs, cpu_count = 1 iff the job is executing.
   More precise than cpu_count_pos_iff_executed when the sequential-job
   assumption is available; useful in service_job_increases_iff_executed proofs. *)
Lemma cpu_count_eq_1_iff_executed : forall m sched j t,
    sequential_jobs m sched ->
    (cpu_count m sched j t = 1 <->
     exists c, c < m /\ sched t c = Some j).
Proof.
  intros m sched j t Hnd.
  split.
  - intros Heq.
    apply cpu_count_pos_iff_executed. lia.
  - intros Hex.
    pose proof (cpu_count_le_1 m sched j t Hnd).
    pose proof (proj2 (cpu_count_pos_iff_executed m sched j t) Hex).
    lia.
Qed.

(* --- Lv.0-1: service_job basics --- *)

Lemma service_job_le_succ : forall m sched j t,
    service_job m sched j t <= service_job m sched j (S t).
Proof.
  intros. rewrite service_job_step. lia.
Qed.

Lemma service_job_monotone : forall m sched j t1 t2,
    t1 <= t2 ->
    service_job m sched j t1 <= service_job m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  induction t2 as [| t2' IH].
  - assert (t1 = 0) by lia. subst. lia.
  - apply Nat.le_succ_r in Hle.
    destruct Hle as [Hle | Heq].
    + eapply Nat.le_trans. apply IH. exact Hle. apply service_job_le_succ.
    + subst. lia.
Qed.

Lemma service_job_increase_at_most_1 : forall m sched j t,
    sequential_jobs m sched ->
    service_job m sched j (S t) <= service_job m sched j t + 1.
Proof.
  intros m sched j t Hnd.
  rewrite service_job_step.
  pose proof (cpu_count_le_1 m sched j t Hnd). lia.
Qed.

Lemma service_job_no_increase_if_not_executed : forall m sched j t,
    (forall c, c < m -> sched t c <> Some j) ->
    service_job m sched j (S t) = service_job m sched j t.
Proof.
  intros m sched j t Hnone.
  rewrite service_job_step.
  apply (proj2 (cpu_count_zero_iff_not_executed m sched j t)) in Hnone.
  lia.
Qed.

Lemma service_job_increases_iff_executed : forall m sched j t,
    sequential_jobs m sched ->
    (service_job m sched j (S t) = service_job m sched j t + 1 <->
     exists c, c < m /\ sched t c = Some j).
Proof.
  intros m sched j t Hnd.
  rewrite service_job_step.
  rewrite <- (cpu_count_eq_1_iff_executed m sched j t Hnd).
  lia.
Qed.

(* --- Lv.0-2: completed/ready consistency --- *)

Lemma completed_not_ready : forall jobs m sched j t,
    completed jobs m sched j t -> ~ready jobs m sched j t.
Proof.
  unfold completed, ready, eligible.
  intros jobs m sched j t Hcomp [[_ Hnot] _].
  exact (Hnot Hcomp).
Qed.

Lemma ready_implies_released : forall jobs m sched j t,
    ready jobs m sched j t -> released jobs j t.
Proof.
  unfold ready, eligible.
  intros jobs m sched j t Hr. exact (proj1 (proj1 Hr)).
Qed.

Lemma ready_implies_not_completed : forall jobs m sched j t,
    ready jobs m sched j t -> ~completed jobs m sched j t.
Proof.
  unfold ready, eligible.
  intros jobs m sched j t Hr. exact (proj2 (proj1 Hr)).
Qed.

Lemma not_ready_before_release : forall jobs m sched j t,
    t < job_release (jobs j) -> ~ready jobs m sched j t.
Proof.
  unfold ready, eligible, released.
  intros jobs m sched j t Hlt [[Hrel _] _]. lia.
Qed.

Lemma completed_monotone : forall jobs m sched j t1 t2,
    t1 <= t2 ->
    completed jobs m sched j t1 ->
    completed jobs m sched j t2.
Proof.
  unfold completed.
  intros jobs m sched j t1 t2 Hle Hcomp.
  eapply Nat.le_trans. exact Hcomp.
  apply service_job_monotone. exact Hle.
Qed.

Lemma eligible_iff_released_and_not_completed : forall jobs m sched j t,
    eligible jobs m sched j t <->
    released jobs j t /\ ~completed jobs m sched j t.
Proof.
  unfold eligible. tauto.
Qed.

Lemma ready_iff_eligible_and_not_running : forall jobs m sched j t,
    ready jobs m sched j t <->
    eligible jobs m sched j t /\ ~running m sched j t.
Proof.
  unfold ready. tauto.
Qed.

(* --- Lv.0-3: valid_schedule basics --- *)

Lemma valid_no_run_before_release : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    job_release (jobs j) <= t.
Proof.
  unfold valid_schedule, eligible, released.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (proj1 (Hv j t c Hlt Hrun)).
Qed.

Lemma valid_no_run_after_completion : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    ~completed jobs m sched j t.
Proof.
  unfold valid_schedule, eligible.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (proj2 (Hv j t c Hlt Hrun)).
Qed.

(* valid_schedule directly implies eligible for any running job.
   (Running jobs satisfy eligible but NOT ready; valid_schedule uses eligible.) *)
Lemma valid_running_implies_eligible : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (Hv j t c Hlt Hrun).
Qed.

(* --- Lv.0-4: pre_release / eligible / ready / running relationships --- *)

(* A pre-release job is not eligible. *)
Lemma pre_release_not_eligible : forall jobs m sched j t,
    pre_release jobs j t ->
    ~eligible jobs m sched j t.
Proof.
  unfold pre_release, eligible, released.
  intros jobs m sched j t Hpend [Hrel _]. lia.
Qed.

(* A pre-release job is not ready. *)
Lemma pre_release_not_ready : forall jobs m sched j t,
    pre_release jobs j t ->
    ~ready jobs m sched j t.
Proof.
  unfold pre_release, ready, eligible, released.
  intros jobs m sched j t Hpend [[Hrel _] _]. lia.
Qed.

(* ready implies not running: a job in the ready/runnable state is not on a CPU. *)
Lemma ready_implies_not_running : forall jobs m sched j t,
    ready jobs m sched j t -> ~running m sched j t.
Proof.
  unfold ready. intros jobs m sched j t [_ H]. exact H.
Qed.

(* running implies not ready: a job currently on a CPU is not in the ready queue. *)
Lemma running_implies_not_ready : forall jobs m sched j t,
    running m sched j t -> ~ready jobs m sched j t.
Proof.
  intros jobs m sched j t Hrun Hready.
  exact (ready_implies_not_running jobs m sched j t Hready Hrun).
Qed.

(* completed implies not eligible. *)
Lemma completed_not_eligible : forall jobs m sched j t,
    completed jobs m sched j t ->
    ~eligible jobs m sched j t.
Proof.
  unfold completed, eligible.
  intros jobs m sched j t Hcomp [_ Hnot].
  exact (Hnot Hcomp).
Qed.


(* eligible implies released. *)
Lemma eligible_after_release : forall jobs m sched j t,
    eligible jobs m sched j t ->
    job_release (jobs j) <= t.
Proof.
  unfold eligible, released.
  intros jobs m sched j t [Hrel _]. exact Hrel.
Qed.

(* ready implies released. *)
Lemma ready_after_release : forall jobs m sched j t,
    ready jobs m sched j t ->
    job_release (jobs j) <= t.
Proof.
  unfold ready, eligible, released.
  intros jobs m sched j t [[Hrel _] _]. exact Hrel.
Qed.

(* Scheduling on a valid CPU implies running. *)
Lemma scheduled_implies_running : forall m sched j t c,
    c < m ->
    sched t c = Some j ->
    running m sched j t.
Proof.
  unfold running.
  intros m sched j t c Hlt Hrun.
  exists c. split. exact Hlt. exact Hrun.
Qed.

(* ===== ScheduleFacts: Service / Completion 補題 etc. ===== *)

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

(* ===== Section 3: remaining_cost and laxity lemmas ===== *)

(* --- remaining_cost basics --- *)

(* remaining_cost is at most job_cost. *)
Lemma remaining_cost_le_cost : forall jobs m sched j t,
    remaining_cost jobs m sched j t <= job_cost (jobs j).
Proof.
  intros jobs m sched j t.
  unfold remaining_cost. lia.
Qed.

(* completed implies remaining_cost = 0. *)
Lemma completed_implies_remaining_cost_zero : forall jobs m sched j t,
    completed jobs m sched j t ->
    remaining_cost jobs m sched j t = 0.
Proof.
  intros jobs m sched j t Hcomp.
  unfold remaining_cost, completed in *.
  lia.
Qed.

(* remaining_cost = 0 implies completed. *)
Lemma remaining_cost_zero_implies_completed : forall jobs m sched j t,
    remaining_cost jobs m sched j t = 0 ->
    completed jobs m sched j t.
Proof.
  intros jobs m sched j t Hz.
  unfold remaining_cost, completed in *.
  lia.
Qed.

(* not completed implies remaining_cost > 0. *)
Lemma not_completed_implies_remaining_cost_pos : forall jobs m sched j t,
    ~ completed jobs m sched j t ->
    remaining_cost jobs m sched j t > 0.
Proof.
  intros jobs m sched j t Hnc.
  unfold remaining_cost, completed in *.
  lia.
Qed.

(* --- 1-step service lemma for the single-CPU case --- *)

(* service_job 1 advances by 1 iff job j ran on CPU 0 at time t. *)
Lemma service_job_step_uni : forall sched j t,
    service_job 1 sched j (S t) =
    service_job 1 sched j t + (if runs_on sched j t 0 then 1 else 0).
Proof.
  intros sched j t.
  rewrite service_job_step.
  simpl cpu_count.
  destruct (runs_on sched j t 0); simpl; lia.
Qed.

(* If j ran at t on CPU 0 and was not yet completed, remaining_cost decreases by 1. *)
Lemma remaining_cost_step_running_uni : forall jobs sched j t,
    sched t 0 = Some j ->
    ~ completed jobs 1 sched j t ->
    remaining_cost jobs 1 sched j (S t) =
    remaining_cost jobs 1 sched j t - 1.
Proof.
  intros jobs sched j t Hrun Hnc.
  unfold remaining_cost.
  rewrite service_job_step_uni.
  assert (Hro : runs_on sched j t 0 = true).
  { apply runs_on_true_iff. exact Hrun. }
  rewrite Hro.
  pose proof (not_completed_implies_remaining_cost_pos jobs 1 sched j t Hnc) as Hpos.
  unfold remaining_cost in Hpos.
  lia.
Qed.

(* If j did not run at t on CPU 0, remaining_cost is unchanged. *)
Lemma remaining_cost_step_not_running_uni : forall jobs sched j t,
    sched t 0 <> Some j ->
    remaining_cost jobs 1 sched j (S t) =
    remaining_cost jobs 1 sched j t.
Proof.
  intros jobs sched j t Hnrun.
  unfold remaining_cost.
  rewrite service_job_step_uni.
  assert (Hro : runs_on sched j t 0 = false).
  { apply runs_on_false_iff. exact Hnrun. }
  rewrite Hro. lia.
Qed.

(* --- laxity basics --- *)

(* Unfold laxity to its definition. *)
Lemma laxity_unfold : forall jobs m sched j t,
    laxity jobs m sched j t =
      (Z.of_nat (job_abs_deadline (jobs j))
      - Z.of_nat t
      - Z.of_nat (remaining_cost jobs m sched j t))%Z.
Proof.
  intros. unfold laxity. reflexivity.
Qed.

(* After completion, remaining_cost = 0, so laxity simplifies. *)
Lemma completed_implies_laxity_deadline_minus_now : forall jobs m sched j t,
    completed jobs m sched j t ->
    laxity jobs m sched j t =
      (Z.of_nat (job_abs_deadline (jobs j)) - Z.of_nat t)%Z.
Proof.
  intros jobs m sched j t Hcomp.
  rewrite laxity_unfold.
  rewrite (completed_implies_remaining_cost_zero jobs m sched j t Hcomp).
  lia.
Qed.

(* --- 1-step laxity change for the single-CPU case --- *)

(* If j ran at t on CPU 0 and was not yet completed:
   time advances by 1, remaining_cost decreases by 1 → laxity unchanged. *)
Lemma laxity_step_running_uni : forall jobs sched j t,
    sched t 0%nat = Some j ->
    ~ completed jobs 1 sched j t ->
    laxity jobs 1 sched j (S t) = laxity jobs 1 sched j t.
Proof.
  intros jobs sched j t Hrun Hnc.
  rewrite !laxity_unfold.
  pose proof (not_completed_implies_remaining_cost_pos jobs 1 sched j t Hnc) as Hpos.
  rewrite (remaining_cost_step_running_uni jobs sched j t Hrun Hnc).
  rewrite Nat2Z.inj_sub by lia.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(* If j did not run at t on CPU 0:
   time advances by 1, remaining_cost unchanged → laxity decreases by 1. *)
Lemma laxity_step_not_running_uni : forall jobs sched j t,
    sched t 0%nat <> Some j ->
    (laxity jobs 1 sched j (S t) = laxity jobs 1 sched j t - 1)%Z.
Proof.
  intros jobs sched j t Hnrun.
  rewrite !laxity_unfold.
  rewrite (remaining_cost_step_not_running_uni jobs sched j t Hnrun).
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

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
