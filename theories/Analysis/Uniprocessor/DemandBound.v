From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.RequestBound.

(* ===== Demand-Bound Function (DBF) ===== *)

(* The periodic DBF counts jobs whose absolute deadline falls within [0, H].
   For a task with relative deadline d and period p:
     dbf(H) = 0                             if H < d
            = S((H - d) / p) * wcet         if H ≥ d

   Unlike the RBF which counts jobs with release < H, the DBF counts jobs
   with absolute deadline ≤ H.  The DBF is the tighter of the two bounds
   and is the key ingredient in processor-demand analysis (e.g., EDF schedulability). *)
Definition periodic_dbf
    (tasks : TaskId -> Task) (τ : TaskId) (H : Time) : nat :=
  if H <? task_relative_deadline (tasks τ) then 0
  else
    (S ((H - task_relative_deadline (tasks τ))
         / task_period (tasks τ)))
    * task_cost (tasks τ).

(* Sporadic tasks satisfy the same demand bound as periodic tasks with the
   same period and relative deadline, since their inter-arrival is at least
   the period and their deadlines are derived by the same formula. *)
Definition sporadic_dbf_bound
    (tasks : TaskId -> Task) (τ : TaskId) (H : Time) : nat :=
  periodic_dbf tasks τ H.

(* Jittered-periodic tasks also satisfy the same demand bound.
   Release jitter can only delay a release, which pushes the absolute deadline
   further out, so the count of jobs with deadline ≤ H can only decrease. *)
Definition jittered_periodic_dbf_bound
    (tasks : TaskId -> Task) (τ : TaskId) (H : Time) : nat :=
  periodic_dbf tasks τ H.

(* ===== Basic properties ===== *)

(* sporadic_dbf_bound and jittered_periodic_dbf_bound are definitionally
   equal to periodic_dbf. *)
Lemma sporadic_dbf_bound_eq_periodic_dbf :
  forall tasks τ H,
    sporadic_dbf_bound tasks τ H = periodic_dbf tasks τ H.
Proof. reflexivity. Qed.

Lemma jittered_periodic_dbf_bound_eq_sporadic_dbf :
  forall tasks τ H,
    jittered_periodic_dbf_bound tasks τ H = sporadic_dbf_bound tasks τ H.
Proof. reflexivity. Qed.

(* The DBF is zero when H is strictly below the relative deadline:
   no job can have an absolute deadline ≤ H if the earliest possible
   absolute deadline is the relative deadline itself (at offset 0). *)
Lemma periodic_dbf_zero_before_deadline :
  forall tasks τ H,
    H < task_relative_deadline (tasks τ) ->
    periodic_dbf tasks τ H = 0.
Proof.
  intros tasks τ H Hlt.
  unfold periodic_dbf.
  apply Nat.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

(* At H = d (the relative deadline), exactly one job can have deadline ≤ H:
   the 0-th job, with deadline = offset + 0*p + d = d (when offset = 0).
   The count is S(0/p) = S(0) = 1, so dbf(d) = 1 * wcet = wcet. *)
Lemma periodic_dbf_at_deadline :
  forall tasks τ,
    0 < task_period (tasks τ) ->
    periodic_dbf tasks τ (task_relative_deadline (tasks τ))
    = task_cost (tasks τ).
Proof.
  intros tasks τ Hp.
  unfold periodic_dbf.
  rewrite Nat.ltb_irrefl.
  replace (task_relative_deadline (tasks τ) - task_relative_deadline (tasks τ)) with 0 by lia.
  rewrite Nat.Div0.div_0_l.
  simpl. lia.
Qed.

Lemma div_le_self :
  forall n d,
    0 < d ->
    n / d <= n.
Proof.
  intros n d Hd.
  pose proof (Nat.div_mod n d) as Hdiv.
  assert (Hd' : d <> 0) by lia.
  specialize (Hdiv Hd').
  assert (Hmul_le : d * (n / d) <= n) by lia.
  destruct (n / d) eqn:Hq.
  - apply Nat.le_0_l.
  - destruct d.
    + lia.
    + lia.
Qed.

Lemma div_mul_le_self :
  forall n d,
    0 < d ->
    d * (n / d) <= n.
Proof.
  intros n d Hd.
  pose proof (Nat.div_mod n d) as Hdiv.
  assert (Hd' : d <> 0) by lia.
  specialize (Hdiv Hd').
  lia.
Qed.

(* ===== Monotonicity ===== *)

(* The count S((H - d) / p) is non-decreasing in H. *)
Lemma periodic_dbf_count_monotone :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H1 H2 : Time),
    H1 <= H2 ->
    (if H1 <? task_relative_deadline (tasks τ) then 0
     else S ((H1 - task_relative_deadline (tasks τ)) / task_period (tasks τ)))
    <=
    (if H2 <? task_relative_deadline (tasks τ) then 0
     else S ((H2 - task_relative_deadline (tasks τ)) / task_period (tasks τ))).
Proof.
  intros tasks τ H1 H2 Hle.
  set (d := task_relative_deadline (tasks τ)).
  set (p := task_period (tasks τ)).
  destruct (Nat.ltb_spec H1 d) as [Hlt1 | Hge1].
  - (* H1 < d: LHS is 0, RHS is ≥ 0 *)
    apply Nat.le_0_l.
  - (* H1 ≥ d *)
    destruct (Nat.ltb_spec H2 d) as [Hlt2 | Hge2].
    + lia.
    + apply le_n_S.
      apply Nat.Div0.div_le_mono.
      lia.
Qed.

Lemma periodic_dbf_monotone :
  forall tasks τ H1 H2,
    H1 <= H2 ->
    periodic_dbf tasks τ H1 <= periodic_dbf tasks τ H2.
Proof.
  intros tasks τ H1 H2 Hle.
  unfold periodic_dbf.
  set (d := task_relative_deadline (tasks τ)).
  set (p := task_period (tasks τ)).
  set (c := task_cost (tasks τ)).
  destruct (Nat.ltb_spec H1 d) as [Hlt1 | Hge1].
  - apply Nat.le_0_l.
  - destruct (Nat.ltb_spec H2 d) as [Hlt2 | Hge2].
    + lia.
    + apply Nat.mul_le_mono_r.
      apply le_n_S.
      apply Nat.Div0.div_le_mono.
      lia.
Qed.

Lemma sporadic_dbf_bound_monotone :
  forall tasks τ H1 H2,
    H1 <= H2 ->
    sporadic_dbf_bound tasks τ H1 <= sporadic_dbf_bound tasks τ H2.
Proof.
  intros tasks τ H1 H2 Hle.
  unfold sporadic_dbf_bound.
  exact (periodic_dbf_monotone tasks τ H1 H2 Hle).
Qed.

(* ===== DBF ≤ RBF ===== *)

(* The DBF count S((H - d) / p) is at most the RBF count ⌈H / p⌉.
   Proof sketch:
     S((H - d) / p) = floor((H - d) / p) + 1
                    ≤ floor((H - 1) / p) + 1    [since d ≥ 1 → H-d ≤ H-1]
                    = ⌈H / p⌉                   [standard identity]
   This requires 0 < task_relative_deadline (d ≥ 1). *)
Lemma periodic_dbf_count_le_rbf_count :
  forall (tasks : TaskId -> Task) (τ : TaskId) (H : Time),
    0 < task_period (tasks τ) ->
    0 < task_relative_deadline (tasks τ) ->
    H >= task_relative_deadline (tasks τ) ->
    S ((H - task_relative_deadline (tasks τ)) / task_period (tasks τ))
    <= (H + task_period (tasks τ) - 1) / task_period (tasks τ).
Proof.
  intros tasks τ H Hp Hd Hge.
  set (d := task_relative_deadline (tasks τ)).
  set (p := task_period (tasks τ)).
  (* We prove: (H - d) / p + 1 ≤ (H + p - 1) / p
     Equivalently: (H - d) / p < (H + p - 1) / p
     Since H - d ≤ H - 1 (as d ≥ 1), it suffices to show
       (H - 1) / p < (H + p - 1) / p + 1, i.e.,
       (H - 1) / p ≤ (H + p - 1) / p, then
       S((H-d)/p) ≤ S((H-1)/p) ≤ ⌈H/p⌉.

     Key identity: floor((H - 1) / p) + 1 = ⌈H / p⌉ for H ≥ 1 and p ≥ 1. *)
  assert (Hd_le : d <= H) by lia.
  assert (Hp0 : p <> 0) by lia.
  (* Step 1: S((H-d)/p) ≤ S((H-1)/p) *)
  assert (Hstep1 : S ((H - d) / p) <= S ((H - 1) / p)).
  {
    apply le_n_S.
    apply Nat.Div0.div_le_mono.
    lia.
  }
  (* Step 2: S((H-1)/p) = ⌈H/p⌉ = (H + p - 1) / p *)
  assert (Hstep2 : S ((H - 1) / p) = (H + p - 1) / p).
  {
    assert (HH : H >= 1) by lia.
    replace (H + p - 1) with (H - 1 + 1 * p) by lia.
    rewrite Nat.div_add by lia.
    lia.
  }
  lia.
Qed.

Lemma periodic_dbf_le_periodic_rbf :
  forall tasks τ H,
    0 < task_period (tasks τ) ->
    0 < task_relative_deadline (tasks τ) ->
    periodic_dbf tasks τ H <= periodic_rbf tasks τ H.
Proof.
  intros tasks τ H Hp Hd.
  unfold periodic_dbf, periodic_rbf.
  destruct (Nat.ltb_spec H (task_relative_deadline (tasks τ))) as [Hlt | Hge].
  - (* H < d: dbf = 0 ≤ rbf *)
    apply Nat.le_0_l.
  - (* H ≥ d: dbf count ≤ rbf count *)
    apply Nat.mul_le_mono_r.
    exact (periodic_dbf_count_le_rbf_count tasks τ H Hp Hd Hge).
Qed.

Lemma sporadic_dbf_bound_le_rbf :
  forall tasks τ H,
    0 < task_period (tasks τ) ->
    0 < task_relative_deadline (tasks τ) ->
    sporadic_dbf_bound tasks τ H <= sporadic_rbf_bound tasks τ H.
Proof.
  intros tasks τ H Hp Hd.
  unfold sporadic_dbf_bound, sporadic_rbf_bound.
  exact (periodic_dbf_le_periodic_rbf tasks τ H Hp Hd).
Qed.
