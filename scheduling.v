From Stdlib Require Import Arith Arith.PeanoNat Lia.

(* ===== Phase 0: Design Decisions ===== *)

Definition JobId : Type := nat.
Definition CPU   : Type := nat.
Definition Time  : Type := nat.

Record Job : Type := mkJob {
  job_release  : Time;
  job_cost     : nat;
  job_deadline : Time;
}.

(* time -> CPU -> option JobId: multicore schedule *)
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

(* Cumulative execution of j in [0,t) across all CPUs 0..m-1 *)
Fixpoint service (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match t with
  | O    => 0
  | S t' => cpu_count sched j t' m + service m sched j t'
  end.

Definition completed (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  service m sched j t >= job_cost (jobs j).

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
   Currently equivalent to pending; can be strengthened later to capture
   precedence constraints, non-preemptive sections, affinity, etc. *)
Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  pending jobs m sched j t.

(* Sequential job model: same job never runs on two CPUs simultaneously.
   For parallel jobs, remove this constraint; service increment bound becomes m. *)
Definition no_duplication (m : nat) (sched : Schedule) : Prop :=
  forall j t c1 c2,
    c1 < m -> c2 < m ->
    sched t c1 = Some j -> sched t c2 = Some j -> c1 = c2.

(* A schedule is valid if every scheduled job is ready at that time.
   This subsumes: no running before release, no running after completion. *)
Definition valid_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j t c, c < m -> sched t c = Some j -> ready jobs m sched j t.

(* A job set is valid when every job has positive cost.
   Zero-cost jobs are immediately completed at t=0 and thus never pending/ready. *)
Definition valid_jobs (jobs : JobId -> Job) : Prop :=
  forall j, 0 < job_cost (jobs j).

(* A job misses its deadline if it is not completed by job_deadline. *)
Definition missed_deadline (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) : Prop :=
  ~completed jobs m sched j (job_deadline (jobs j)).

(* A schedule is feasible if no job misses its deadline. *)
Definition schedulable (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, ~missed_deadline jobs m sched j.

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

(* --- service lemmas --- *)

(* Matches the Fixpoint definition order exactly *)
Lemma service_unfold : forall m sched j t,
    service m sched j (S t) = cpu_count sched j t m + service m sched j t.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Commuted form; use this for rewriting when the sum order matters *)
Lemma service_step : forall m sched j t,
    service m sched j (S t) = service m sched j t + cpu_count sched j t m.
Proof.
  intros. rewrite service_unfold. lia.
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
  - intros H. apply cpu_count_pos_iff_executed. lia.
  - intros H. apply cpu_count_pos_iff_executed in H. lia.
Qed.

(* Under no_duplication, cpu_count <= 1 *)
Lemma cpu_count_le_1 : forall m sched j t,
    no_duplication m sched ->
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
      assert (Hnd' : no_duplication m' sched).
      { intros j0 t0 c1 c2 H1 H2 H3 H4.
        apply (Hnd j0 t0 c1 c2).
        - lia.
        - lia.
        - exact H3.
        - exact H4. }
      exact (IH sched j t Hnd').
Qed.

(* Stronger form: cpu_count is exactly 0 or 1 under no_duplication *)
Lemma cpu_count_0_or_1 : forall m sched j t,
    no_duplication m sched ->
    cpu_count sched j t m = 0 \/ cpu_count sched j t m = 1.
Proof.
  intros m sched j t Hnd.
  pose proof (cpu_count_le_1 m sched j t Hnd) as Hle.
  destruct (cpu_count sched j t m) as [| n].
  - left. reflexivity.
  - right. lia.
Qed.

(* --- Lv.0-1: service basics --- *)

Lemma service_le_succ : forall m sched j t,
    service m sched j t <= service m sched j (S t).
Proof.
  intros. rewrite service_step. lia.
Qed.

Lemma service_monotone : forall m sched j t1 t2,
    t1 <= t2 ->
    service m sched j t1 <= service m sched j t2.
Proof.
  intros m sched j t1 t2 Hle.
  induction t2 as [| t2' IH].
  - assert (t1 = 0) by lia. subst. lia.
  - apply Nat.le_succ_r in Hle.
    destruct Hle as [Hle | Heq].
    + eapply Nat.le_trans. apply IH. exact Hle. apply service_le_succ.
    + subst. lia.
Qed.

Lemma service_increase_at_most_1 : forall m sched j t,
    no_duplication m sched ->
    service m sched j (S t) <= service m sched j t + 1.
Proof.
  intros m sched j t Hnd.
  rewrite service_step.
  pose proof (cpu_count_le_1 m sched j t Hnd). lia.
Qed.

Lemma service_no_increase_if_not_executed : forall m sched j t,
    (forall c, c < m -> sched t c <> Some j) ->
    service m sched j (S t) = service m sched j t.
Proof.
  intros m sched j t Hnone.
  rewrite service_step.
  apply (proj2 (cpu_count_zero_iff_not_executed m sched j t)) in Hnone.
  lia.
Qed.

Lemma service_increases_iff_executed : forall m sched j t,
    no_duplication m sched ->
    (service m sched j (S t) = service m sched j t + 1 <->
     exists c, c < m /\ sched t c = Some j).
Proof.
  intros m sched j t Hnd.
  rewrite service_step.
  split.
  - intros Heq.
    apply (proj1 (cpu_count_pos_iff_executed m sched j t)).
    pose proof (cpu_count_le_1 m sched j t Hnd). lia.
  - intros Hexists.
    apply (proj2 (cpu_count_pos_iff_executed m sched j t)) in Hexists.
    pose proof (cpu_count_le_1 m sched j t Hnd). lia.
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
  apply service_monotone. exact Hle.
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
