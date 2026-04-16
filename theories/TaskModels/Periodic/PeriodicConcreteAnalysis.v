From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

(* A first bounded checker for concrete periodic DBF goals. The point set is a
   sound superset of all relevant times up to H: we simply enumerate every time
   in [0, H]. *)
Definition critical_dbf_points_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : list Time :=
  seq 0 (S H).

Definition dbf_test_upto
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb (fun t => taskset_periodic_dbf tasks enumT t <=? t)
          (critical_dbf_points_upto tasks (fun _ => 0) enumT H).

Definition window_dbf_test_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : bool :=
  forallb
    (fun t1 =>
       forallb
         (fun t2 =>
            taskset_periodic_dbf_window tasks offset enumT t1 t2 <=? t2 - t1)
         (seq t1 (S (H - t1))))
    (critical_dbf_points_upto tasks offset enumT H).

Lemma critical_dbf_points_upto_complete :
  forall tasks offset enumT H t,
    t <= H ->
    In t (critical_dbf_points_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H t Hle.
  unfold critical_dbf_points_upto.
  rewrite in_seq.
  lia.
Qed.

Lemma window_dbf_test_upto_inner_complete :
  forall H t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    In t2 (seq t1 (S (H - t1))).
Proof.
  intros H t1 t2 Hle12 Hle2H.
  rewrite in_seq.
  lia.
Qed.

Lemma dbf_test_upto_sound :
  forall tasks enumT H t,
    dbf_test_upto tasks enumT H = true ->
    In t (critical_dbf_points_upto tasks (fun _ => 0) enumT H) ->
    taskset_periodic_dbf tasks enumT t <= t.
Proof.
  intros tasks enumT H t Htest Hin.
  unfold dbf_test_upto in Htest.
  apply forallb_forall with (x := t) in Htest; auto.
  now apply Nat.leb_le in Htest.
Qed.

Theorem dbf_test_upto_true_implies_bounded_dbf :
  forall tasks enumT H t,
    dbf_test_upto tasks enumT H = true ->
    t <= H ->
    taskset_periodic_dbf tasks enumT t <= t.
Proof.
  intros tasks enumT H t Htest Hle.
  eapply dbf_test_upto_sound; eauto.
  apply critical_dbf_points_upto_complete; exact Hle.
Qed.

Lemma window_dbf_test_upto_sound :
  forall tasks offset enumT H t1 t2,
    window_dbf_test_upto tasks offset enumT H = true ->
    In t1 (critical_dbf_points_upto tasks offset enumT H) ->
    In t2 (seq t1 (S (H - t1))) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT H t1 t2 Htest Ht1 Ht2.
  unfold window_dbf_test_upto in Htest.
  apply forallb_forall with (x := t1) in Htest; auto.
  apply forallb_forall with (x := t2) in Htest; auto.
  now apply Nat.leb_le in Htest.
Qed.

Theorem window_dbf_test_upto_true_implies_bounded_window_dbf :
  forall tasks offset enumT H t1 t2,
    window_dbf_test_upto tasks offset enumT H = true ->
    t1 <= t2 ->
    t2 <= H ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT H t1 t2 Htest Hle12 Hle2H.
  eapply window_dbf_test_upto_sound; eauto.
  - apply critical_dbf_points_upto_complete. lia.
  - apply window_dbf_test_upto_inner_complete; assumption.
Qed.

Fixpoint periodic_hyperperiod
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 1
  | τ :: enumT' => Nat.lcm (task_period (tasks τ)) (periodic_hyperperiod tasks enumT')
  end.

Fixpoint periodic_max_relative_deadline
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : Time :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      Nat.max (task_relative_deadline (tasks τ))
              (periodic_max_relative_deadline tasks enumT')
  end.

Fixpoint hyperperiod_load
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (hp : Time) : nat :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      (hp / task_period (tasks τ)) * task_cost (tasks τ) +
      hyperperiod_load tasks enumT' hp
  end.

Definition scalar_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : Time :=
  periodic_max_relative_deadline tasks enumT +
  S (periodic_max_relative_deadline tasks enumT) *
  periodic_hyperperiod tasks enumT.

Definition dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : bool :=
  dbf_test_upto tasks enumT (scalar_dbf_cutoff_bound tasks enumT).

Lemma periodic_hyperperiod_positive :
  forall tasks enumT,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    0 < periodic_hyperperiod tasks enumT.
Proof.
  intros tasks enumT Hpos.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - assert (Hτ : 0 < task_period (tasks τ)).
    { apply Hpos. now left. }
    assert (Htail : 0 < periodic_hyperperiod tasks enumT).
    {
      apply IH.
      intros τ' Hin.
      apply Hpos.
      now right.
    }
    destruct (Nat.eq_dec (Nat.lcm (task_period (tasks τ)) (periodic_hyperperiod tasks enumT)) 0) as [Hlcm|Hlcm].
    + apply Nat.lcm_eq_0 in Hlcm.
      lia.
    + lia.
Qed.

Lemma periodic_hyperperiod_divides :
  forall tasks enumT τ,
    In τ enumT ->
    Nat.divide (task_period (tasks τ)) (periodic_hyperperiod tasks enumT).
Proof.
  intros tasks enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.divide_lcm_l.
    + eapply Nat.divide_trans.
      * apply IH. exact Hin.
      * apply Nat.divide_lcm_r.
Qed.

Lemma periodic_max_relative_deadline_ge :
  forall tasks enumT τ,
    In τ enumT ->
    task_relative_deadline (tasks τ) <= periodic_max_relative_deadline tasks enumT.
Proof.
  intros tasks enumT τ Hin.
  induction enumT as [|τ' enumT IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma periodic_dbf_add_hyperperiod_after_deadline :
  forall tasks τ t hp,
    task_relative_deadline (tasks τ) <= t ->
    0 < task_period (tasks τ) ->
    Nat.divide (task_period (tasks τ)) hp ->
    periodic_dbf tasks τ (t + hp) =
    periodic_dbf tasks τ t +
    (hp / task_period (tasks τ)) * task_cost (tasks τ).
Proof.
  intros tasks τ t hp Hdl Hp Hdiv.
  unfold periodic_dbf.
  assert (Ht :
    (t <? task_relative_deadline (tasks τ)) = false).
  { apply Nat.ltb_ge. lia. }
  assert (Hthp :
    (t + hp <? task_relative_deadline (tasks τ)) = false).
  { apply Nat.ltb_ge. lia. }
  rewrite Ht, Hthp.
  replace
    (t + hp - task_relative_deadline (tasks τ))
    with
    ((t - task_relative_deadline (tasks τ)) + hp) by lia.
  replace
    (((t - task_relative_deadline (tasks τ)) + hp) / task_period (tasks τ))
    with
    (((t - task_relative_deadline (tasks τ)) / task_period (tasks τ)) +
     (hp / task_period (tasks τ))).
  2:{
    destruct Hdiv as [k Hk].
    rewrite Hk.
    rewrite (Nat.div_add (t - task_relative_deadline (tasks τ))
                         k
                         (task_period (tasks τ))) by lia.
    rewrite Nat.div_mul by lia.
    reflexivity.
  }
  nia.
Qed.

Lemma taskset_periodic_dbf_add_hyperperiod_after_deadline :
  forall tasks enumT t hp,
    (forall τ, In τ enumT -> task_relative_deadline (tasks τ) <= t) ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp) ->
    taskset_periodic_dbf tasks enumT (t + hp) =
    taskset_periodic_dbf tasks enumT t + hyperperiod_load tasks enumT hp.
Proof.
  intros tasks enumT t hp Hdl Hp Hdiv.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - rewrite periodic_dbf_add_hyperperiod_after_deadline.
    + rewrite IH.
      * lia.
      * intros τ' Hin.
        apply Hdl.
        now right.
      * intros τ' Hin.
        apply Hp.
        now right.
      * intros τ' Hin.
        apply Hdiv.
        now right.
    + apply Hdl. now left.
    + apply Hp. now left.
    + apply Hdiv. now left.
Qed.

Lemma taskset_periodic_dbf_add_hyperperiod_after_deadline_n :
  forall tasks enumT t hp q,
    (forall τ, In τ enumT -> task_relative_deadline (tasks τ) <= t) ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    (forall τ, In τ enumT -> Nat.divide (task_period (tasks τ)) hp) ->
    taskset_periodic_dbf tasks enumT (t + q * hp) =
    taskset_periodic_dbf tasks enumT t + q * hyperperiod_load tasks enumT hp.
Proof.
  intros tasks enumT t hp q Hdl Hp Hdiv.
  induction q as [|q IH].
  - replace (t + 0 * hp) with t by lia.
    lia.
  - replace (t + S q * hp) with ((t + q * hp) + hp) by lia.
    rewrite taskset_periodic_dbf_add_hyperperiod_after_deadline.
    + rewrite IH.
      lia.
    + intros τ Hin.
      specialize (Hdl τ Hin).
      lia.
    + exact Hp.
    + exact Hdiv.
Qed.

Lemma hyperperiod_load_le_hyperperiod :
  forall tasks enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    dbf_test_by_cutoff tasks enumT = true ->
    hyperperiod_load tasks enumT (periodic_hyperperiod tasks enumT) <=
    periodic_hyperperiod tasks enumT.
Proof.
  intros tasks enumT Hnodup Hpos Htest.
  set (m := periodic_max_relative_deadline tasks enumT).
  set (hp := periodic_hyperperiod tasks enumT).
  assert (Hdbf_big :
    taskset_periodic_dbf tasks enumT (m + S m * hp) <= m + S m * hp).
  {
    apply (dbf_test_upto_true_implies_bounded_dbf tasks enumT (m + S m * hp) (m + S m * hp)).
    - exact Htest.
    - lia.
  }
  assert (Hperiodic :
    taskset_periodic_dbf tasks enumT (m + S m * hp) =
    taskset_periodic_dbf tasks enumT m +
    S m * hyperperiod_load tasks enumT hp).
  {
    eapply (taskset_periodic_dbf_add_hyperperiod_after_deadline_n
              tasks enumT m hp (S m)).
    - intros τ Hin.
      unfold m.
      apply periodic_max_relative_deadline_ge.
      exact Hin.
    - exact Hpos.
    - intros τ Hin.
      unfold hp.
      apply periodic_hyperperiod_divides.
      exact Hin.
  }
  rewrite Hperiodic in Hdbf_big.
  assert (Hnonneg :
    0 <= taskset_periodic_dbf tasks enumT m).
  { lia. }
  clear Hperiodic.
  nia.
Qed.

Theorem dbf_test_by_cutoff_sound :
  forall tasks enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    dbf_test_by_cutoff tasks enumT = true ->
    forall t,
      taskset_periodic_dbf tasks enumT t <= t.
Proof.
  intros tasks enumT Hnodup Hpos Htest t.
  set (m := periodic_max_relative_deadline tasks enumT).
  set (hp := periodic_hyperperiod tasks enumT).
  set (load := hyperperiod_load tasks enumT hp).
  set (cutoff := m + S m * hp).
  destruct (le_gt_dec t (m + hp)) as [Hle | Hgt].
  - apply (dbf_test_upto_true_implies_bounded_dbf tasks enumT cutoff t).
    + exact Htest.
    + unfold cutoff. lia.
  - assert (Hhp_pos : 0 < hp).
    {
      unfold hp.
      apply periodic_hyperperiod_positive.
      exact Hpos.
    }
    set (delta := t - m).
    set (q := delta / hp).
    set (r := delta mod hp).
    set (base := m + r).
    assert (Hbase_ge : m <= base).
    { unfold base. lia. }
    assert (Hbase_le : base <= m + hp).
    {
      assert (Hneq : hp <> 0) by lia.
      assert (Hr : r < hp).
      {
        unfold r.
        apply Nat.mod_upper_bound.
        exact Hneq.
      }
      unfold base.
      apply Nat.lt_succ_r.
      lia.
    }
    assert (Hbase_eq :
      t = base + q * hp).
    {
      unfold base, q, r, delta.
      pose proof (Nat.div_mod (t - m) hp) as Hdivmod.
      assert (Hneq : hp <> 0) by lia.
      specialize (Hdivmod Hneq).
      lia.
    }
    assert (Hload_le : load <= hp).
    {
      unfold load.
      apply hyperperiod_load_le_hyperperiod; assumption.
    }
    assert (Hbase_dbf :
      taskset_periodic_dbf tasks enumT base <= base).
    {
      apply (dbf_test_upto_true_implies_bounded_dbf tasks enumT cutoff base).
      - exact Htest.
      - unfold cutoff. lia.
    }
    rewrite Hbase_eq.
    rewrite taskset_periodic_dbf_add_hyperperiod_after_deadline_n.
    + nia.
    + intros τ Hin.
      eapply Nat.le_trans.
      * apply periodic_max_relative_deadline_ge.
        exact Hin.
      * exact Hbase_ge.
    + exact Hpos.
    + intros τ Hin.
      unfold hp.
      apply periodic_hyperperiod_divides.
      exact Hin.
Qed.

Theorem dbf_check_by_cutoff :
  forall tasks enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    dbf_test_by_cutoff tasks enumT = true ->
    forall t,
      taskset_periodic_dbf tasks enumT t <= t.
Proof.
  exact dbf_test_by_cutoff_sound.
Qed.
