From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
Require Import Base.
(* Note: Base.pre_release (t < release_time, schedule-independent) is now in scope.
   Schedule.eligible (released AND NOT completed) is the dispatch condition for
   valid_schedule; running jobs satisfy eligible but NOT ready.
   Schedule.ready (eligible AND NOT running) is the classical ready-queue state. *)

(* ===== Phase 1: Core Definitions ===== *)

(* Bool indicator: is job j running on cpu c at time t? *)
Definition runs_on (sched : Schedule) (j : JobId) (t : Time) (c : CPU) : bool :=
  match sched t c with
  | Some j' => Nat.eqb j' j
  | None    => false
  end.

(* Count CPUs in 0..m-1 running job j at time t *)
Fixpoint cpu_count (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match m with
  | O    => 0
  | S m' => (if runs_on sched j t m' then 1 else 0) + cpu_count m' sched j t
  end.

(* job-level 累積実行量: [0,t) の全 CPU での job j の総実行ステップ数。
   DAG では node ごとの service (service_node) が別途必要になる。
   この定義は job 全体の work を測る service_job として命名する。 *)
Fixpoint service_job (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match t with
  | O    => 0
  | S t' => cpu_count m sched j t' + service_job m sched j t'
  end.

(* `completed jobs m sched j t` means job j has received >= job_cost units of
   service in [0,t).  Equivalently: "completed by the start of time slot t". *)
Definition completed (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  service_job m sched j t >= job_cost (jobs j).

(* A job is running at time t on some valid CPU in 0..m-1. *)
Definition running (m : nat) (sched : Schedule) (j : JobId) (t : Time) : Prop :=
  exists c : CPU, c < m /\ sched t c = Some j.

(* A job is eligible: released and not yet completed.
   This is the minimum condition for CPU assignment; running jobs satisfy
   eligible. valid_schedule is stated in terms of eligible, not ready,
   because a running job is eligible but NOT ready (ready requires
   NOT running). Zero-cost jobs are immediately completed at t=0 and thus
   never eligible; use valid_jobs to exclude them when needed. *)
Definition eligible (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  released jobs j t /\ ~completed jobs m sched j t.

(* A job is ready: eligible AND not currently executing on any CPU.
   This is the classical "ready queue" state: a job waiting to be scheduled.
   Contrast with eligible, which covers both running and waiting jobs.
   Future DAG extensions will refine this to: eligible AND all predecessors
   completed AND not running. *)
Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  eligible jobs m sched j t /\ ~running m sched j t.

(* Sequential-job 仮定: 同じ job は同時に複数 CPU で走らない。
   DAG job ではこの制約は job 単位ではなく node 単位になる:
     - 同じ node は同時に複数 CPU で走らない
     - 同じ job の異なる ready node は別 CPU で同時に走ってよい
   DAG 導入時にはこの定義を node-level に置き換える。 *)
Definition sequential_jobs (m : nat) (sched : Schedule) : Prop :=
  forall j t c1 c2,
    c1 < m -> c2 < m ->
    sched t c1 = Some j -> sched t c2 = Some j -> c1 = c2.

(* A schedule is valid if every scheduled job is eligible at that time.
   This subsumes: no running before release, no running after completion.
   Note: scheduled (running) jobs satisfy eligible (released AND NOT completed)
   but NOT ready (ready additionally requires NOT running), so
   valid_schedule is expressed in terms of eligible, not ready. *)
Definition valid_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j t c, c < m -> sched t c = Some j -> eligible jobs m sched j t.

(* A job misses its deadline if it is not completed by job_abs_deadline. *)
Definition missed_deadline (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) : Prop :=
  ~completed jobs m sched j (job_abs_deadline (jobs j)).

(* A schedule is feasible if no job misses its deadline.
   Total-function version: quantifies over all JobId. *)
Definition feasible_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, ~missed_deadline jobs m sched j.

(* A job set is feasible if there exists a valid, feasible schedule.
   Total-function version: quantifies over all JobId.
   For finite/subset reasoning, use feasible_on. *)
Definition feasible (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched, valid_schedule jobs m sched /\ feasible_schedule jobs m sched.

(* Restrict feasibility to a designated job set J.
   This is a forward-compatible layer for moving from the current
   total-function model to finite job-set reasoning. *)
Definition feasible_schedule_on (J : JobId -> Prop)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, J j -> ~missed_deadline jobs m sched j.

Definition feasible_on (J : JobId -> Prop)
    (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched, valid_schedule jobs m sched /\ feasible_schedule_on J jobs m sched.

(* Abstract scheduler: maps a job set and CPU count to a schedule. *)
Parameter Scheduler : Type.
Parameter run_scheduler : Scheduler -> (JobId -> Job) -> nat -> Schedule.

(* A job set is schedulable by algorithm alg if the produced schedule
   is valid and feasible. *)
Definition schedulable_by
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  valid_schedule jobs m (run_scheduler alg jobs m) /\
  feasible_schedule jobs m (run_scheduler alg jobs m).

(* Subset variant: schedulable by alg restricted to job set J. *)
Definition schedulable_by_on (J : JobId -> Prop)
    (alg : Scheduler) (jobs : JobId -> Job) (m : nat) : Prop :=
  valid_schedule jobs m (run_scheduler alg jobs m) /\
  feasible_schedule_on J jobs m (run_scheduler alg jobs m).

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

(* --- Lv.0-5: schedulable_by / schedulable_by_on --- *)

(* schedulable_by implies feasible: the produced schedule witnesses existence. *)
Lemma schedulable_by_implies_feasible :
    forall alg jobs m,
      schedulable_by alg jobs m -> feasible jobs m.
Proof.
  intros alg jobs m [Hvalid Hfeas].
  unfold feasible.
  exists (run_scheduler alg jobs m).
  split; assumption.
Qed.

(* schedulable_by implies schedulable_by_on for any job subset J. *)
Lemma schedulable_by_implies_schedulable_by_on :
    forall (J : JobId -> Prop) alg jobs m,
      schedulable_by alg jobs m -> schedulable_by_on J alg jobs m.
Proof.
  intros J alg jobs m [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j _HJ. exact (Hfeas j).
Qed.

(* schedulable_by_on is monotone: narrowing the job set preserves schedulability. *)
Lemma schedulable_by_on_monotone :
    forall (J J' : JobId -> Prop) alg jobs m,
      (forall j, J j -> J' j) ->
      schedulable_by_on J' alg jobs m ->
      schedulable_by_on J alg jobs m.
Proof.
  intros J J' alg jobs m Hsubset [Hvalid Hfeas].
  unfold schedulable_by_on, feasible_schedule_on.
  split.
  - exact Hvalid.
  - intros j HJ. exact (Hfeas j (Hsubset j HJ)).
Qed.
