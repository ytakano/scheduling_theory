From Stdlib Require Import Arith Arith.PeanoNat Lia.

(* ===== Phase 0: Design Decisions ===== *)

(* === DAG 拡張に向けた設計メモ ===
   将来的には実行単位を 3 層に分ける:
     Task  : 周期的な生成ルール
     Job   : Task の具体的な実行インスタンス
     Node  : Job 内部の並列実行ノード（DAG ノード）

   現在は Node を導入しておらず、実行単位 = Job。
   DAG 導入時には Schedule の型が
     Time -> CPU -> option JobId
   から
     Time -> CPU -> option NodeId  (または option (JobId * NodeId))
   へ移行する可能性がある。

   各定義の DAG 拡張方針は個別のコメントに記載する。 *)

Definition JobId  : Type := nat.
Definition TaskId : Type := nat.
Definition CPU    : Type := nat.
Definition Time   : Type := nat.

(* Task: periodic task as a generation rule for jobs.
   Not yet used in proofs; defined here as a skeleton for future
   periodic scheduling theory (utilization bounds, EDF optimality, etc.). *)
Record Task : Type := mkTask {
  task_cost     : nat;  (* WCET: worst-case execution time per job *)
  task_period   : nat;  (* period: minimum inter-arrival time *)
  task_relative_deadline : nat;  (* relative deadline *)
}.

(* Job: a concrete execution instance, optionally tied to a Task.
   job_task / job_index are unused by current lemmas and may be
   set to 0 for standalone jobs.  They exist so that periodic-task
   extensions can attach identity without restructuring this record. *)
Record Job : Type := mkJob {
  job_task         : TaskId; (* which task generated this job (0 = anonymous) *)
  job_index        : nat;    (* k-th job of that task, 0-indexed (instance number) *)
  job_release      : Time;   (* absolute release time *)
  job_cost         : nat;    (* execution time required by this job *)
  job_abs_deadline : Time;   (* absolute deadline *)
}.

(* time -> CPU -> option JobId: multicore schedule.
   Sequential-job モデルでは実行単位 = job。
   DAG 導入時には option NodeId または option (JobId * NodeId) に移行予定。 *)
Definition Schedule : Type := Time -> CPU -> option JobId.

(* ===== Phase 1: Core Definitions ===== *)

(* Bool indicator: is job j running on cpu c at time t? *)
Definition runs_on (sched : Schedule) (j : JobId) (t : Time) (c : CPU) : bool :=
  match sched t c with
  | Some j' => Nat.eqb j' j
  | None    => false
  end.

(* Count CPUs in 0..m-1 running job j at time t *)
Fixpoint cpu_count (sched : Schedule) (j : JobId) (t : Time) (m : nat) : nat :=
  match m with
  | O    => 0
  | S m' => (if runs_on sched j t m' then 1 else 0) + cpu_count sched j t m'
  end.

(* job-level 累積実行量: [0,t) の全 CPU での job j の総実行ステップ数。
   DAG では node ごとの service (service_node) が別途必要になる。
   この定義は job 全体の work を測る service_job として命名する。 *)
Fixpoint service_job (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match t with
  | O    => 0
  | S t' => cpu_count sched j t' m + service_job m sched j t'
  end.

(* `completed jobs m sched j t` means job j has received >= job_cost units of
   service in [0,t).  Equivalently: "completed by the start of time slot t". *)
Definition completed (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  service_job m sched j t >= job_cost (jobs j).

(* A job has been released at time t *)
Definition released (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  job_release (jobs j) <= t.

(* A job is pending: released and not yet completed.
   Note: a zero-cost job is immediately completed at t=0, so it is never pending.
   Use valid_jobs to exclude zero-cost jobs when needed. *)
Definition pending (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  released jobs j t /\ ~completed jobs m sched j t.

(* A job is ready to execute.
   現在は pending と等価。DAG 拡張時には node 単位の ready になる:
     ready_node n t = pending_node n t /\ preds_completed n t
   job-level ready はその後 "すべての ready node を持つ" などに変わる可能性がある。 *)
Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  pending jobs m sched j t.

(* Sequential-job 仮定: 同じ job は同時に複数 CPU で走らない。
   DAG job ではこの制約は job 単位ではなく node 単位になる:
     - 同じ node は同時に複数 CPU で走らない
     - 同じ job の異なる ready node は別 CPU で同時に走ってよい
   DAG 導入時にはこの定義を node-level に置き換える。 *)
Definition sequential_jobs (m : nat) (sched : Schedule) : Prop :=
  forall j t c1 c2,
    c1 < m -> c2 < m ->
    sched t c1 = Some j -> sched t c2 = Some j -> c1 = c2.

(* A schedule is valid if every scheduled job is ready at that time.
   This subsumes: no running before release, no running after completion. *)
Definition valid_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j t c, c < m -> sched t c = Some j -> ready jobs m sched j t.

(* A job set is valid when every job has positive cost.
   Zero-cost jobs are immediately completed at t=0 and thus never pending/ready.
   This predicate will be used by periodic job generation (Phase 12+):
   e.g. "released directly implies potentially ready" relies on 0 < job_cost. *)
Definition valid_jobs (jobs : JobId -> Job) : Prop :=
  forall j, 0 < job_cost (jobs j).

(* Relationship between Task and Job: a job j belongs to task τ if
   job_task (jobs j) = τ.  Periodic-task constraints (release pattern,
   relative deadline → absolute deadline) will be expressed via
   valid_job_of_task below. *)

(* Skeleton predicate: job j is consistent with its task's parameters.
   This captures "parameter compatibility" only:
     - absolute deadline = release + relative deadline
     - job cost ≤ task WCET
   It does NOT encode the periodic generation rule
     job_release = offset + job_index * task_period
   nor job_index monotonicity nor intra-task job uniqueness.
   Those constraints belong to a separate `periodic_job_generation`
   predicate, introduced in Phase 12 (periodic task theory).
   See also: plan/roadmap.md §12.5. *)
Definition valid_job_of_task (tasks : TaskId -> Task) (jobs : JobId -> Job)
    (j : JobId) : Prop :=
  let τ := job_task (jobs j) in
  job_abs_deadline (jobs j) =
    job_release (jobs j) + task_relative_deadline (tasks τ) /\
  job_cost (jobs j) <= task_cost (tasks τ).

(* A job misses its deadline if it is not completed by job_abs_deadline. *)
Definition missed_deadline (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) : Prop :=
  ~completed jobs m sched j (job_abs_deadline (jobs j)).

(* A schedule is feasible if no job misses its deadline. *)
Definition feasible (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, ~missed_deadline jobs m sched j.

(* A job set is schedulable if there exists a valid, feasible schedule.
   Currently quantifies over all JobId (total function model).
   Future: restrict to a finite job set J : JobId -> Prop or a list,
   so that schedulable / feasible apply only to the jobs in J. *)
Definition schedulable (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched, valid_schedule jobs m sched /\ feasible jobs m sched.

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
    service_job m sched j (S t) = cpu_count sched j t m + service_job m sched j t.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Commuted form; use this for rewriting when the sum order matters *)
Lemma service_job_step : forall m sched j t,
    service_job m sched j (S t) = service_job m sched j t + cpu_count sched j t m.
Proof.
  intros. rewrite service_job_unfold. lia.
Qed.

(* --- cpu_count characterization lemmas --- *)

Lemma cpu_count_zero_iff_not_executed : forall m sched j t,
    cpu_count sched j t m = 0 <->
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

Lemma cpu_count_pos_iff_executed : forall m sched j t,
    0 < cpu_count sched j t m <->
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
        assert (Hpos : 0 < cpu_count sched j t m').
        { apply (proj2 (IH sched j t)). exists c. split. exact Hlt'. exact Hrun. }
        destruct (runs_on sched j t m'); simpl; lia.
Qed.

(* Equivalent to cpu_count_pos_iff_executed; useful when lia cannot close goals
   involving strict positivity, e.g. when rewriting with Nat.neq_0_lt_0. *)
Lemma cpu_count_nonzero_iff_executed : forall m sched j t,
    cpu_count sched j t m <> 0 <->
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
    cpu_count sched j t m <= 1.
Proof.
  induction m as [| m' IH]; intros sched j t Hnd.
  - simpl. lia.
  - simpl.
    destruct (runs_on sched j t m') eqn:Erun.
    + (* runs_on = true: cpu_count m' must be 0 *)
      apply runs_on_true_iff in Erun.
      simpl.
      assert (Hzero : cpu_count sched j t m' = 0).
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
    cpu_count sched j t m = 0 \/ cpu_count sched j t m = 1.
Proof.
  intros m sched j t Hnd.
  pose proof (cpu_count_le_1 m sched j t Hnd) as Hle.
  destruct (cpu_count sched j t m) as [| n].
  - left. reflexivity.
  - right. lia.
Qed.

(* Under sequential_jobs, cpu_count = 1 iff the job is executing.
   More precise than cpu_count_pos_iff_executed when the sequential-job
   assumption is available; useful in service_job_increases_iff_executed proofs. *)
Lemma cpu_count_eq_1_iff_executed : forall m sched j t,
    sequential_jobs m sched ->
    (cpu_count sched j t m = 1 <->
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
  unfold completed, ready, pending.
  intros jobs m sched j t Hcomp [_ Hnot].
  exact (Hnot Hcomp).
Qed.

Lemma not_ready_before_release : forall jobs m sched j t,
    t < job_release (jobs j) -> ~ready jobs m sched j t.
Proof.
  unfold ready, pending, released.
  intros jobs m sched j t Hlt [Hrel _]. lia.
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

Lemma ready_iff_released_and_not_completed : forall jobs m sched j t,
    ready jobs m sched j t <->
    released jobs j t /\ ~completed jobs m sched j t.
Proof.
  unfold ready, pending. tauto.
Qed.

(* --- Lv.0-3: valid_schedule basics --- *)

Lemma valid_no_run_before_release : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    job_release (jobs j) <= t.
Proof.
  unfold valid_schedule, ready, pending, released.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (proj1 (Hv j t c Hlt Hrun)).
Qed.

Lemma valid_no_run_after_completion : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    ~completed jobs m sched j t.
Proof.
  unfold valid_schedule, ready, pending.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (proj2 (Hv j t c Hlt Hrun)).
Qed.

Lemma valid_running_implies_ready : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    ready jobs m sched j t.
Proof.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (Hv j t c Hlt Hrun).
Qed.

(* Convenience form: directly obtains pending without unfolding ready.
   Currently valid because ready = pending definitionally
   (both reduce to released /\ ~completed).
   WARNING: this lemma may break when DAG tasks are introduced,
   since ready will gain a preds_completed clause and will no longer
   be definitionally equal to pending.  Treat as a convenience lemma
   for the current sequential-job layer only. *)
Lemma valid_running_implies_pending : forall jobs m sched j t c,
    valid_schedule jobs m sched ->
    c < m ->
    sched t c = Some j ->
    pending jobs m sched j t.
Proof.
  intros jobs m sched j t c Hv Hlt Hrun.
  exact (Hv j t c Hlt Hrun).
Qed.
