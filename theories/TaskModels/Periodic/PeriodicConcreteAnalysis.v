From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.
From RocqSched Require Import Analysis.Uniprocessor.EDFProcessorDemand.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.
From RocqSched Require Import Uniprocessor.Policies.EDF.

Import ListNotations.

Definition generated_periodic_edf_finite_enumJ
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
  : list JobId :=
  enum_periodic_jobs_upto T tasks offset jobs H enumT codec.

Definition generated_periodic_edf_schedule_on_finite_horizon
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
  : Schedule :=
  generated_schedule
    edf_generic_spec
    (enum_candidates_of
       (generated_periodic_edf_finite_enumJ T tasks offset jobs H enumT codec))
    jobs.

Definition bounded_time_points (H : Time) : list Time :=
  seq 0 (S H).

Definition task_release_points_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : list Time :=
  filter (fun t => t <=? H)
         (map (expected_release tasks offset τ)
              (bounded_time_points H)).

Definition task_deadline_points_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : list Time :=
  filter (fun t => t <=? H)
         (map (expected_abs_deadline tasks offset τ)
              (bounded_time_points H)).

(* A conservative finite search space for concrete periodic DBF goals.
   We expose release/deadline-shaped points explicitly, but we also keep the
   entire bounded range [0, H] so bounded completeness remains constructive and
   proof-friendly in v1. *)
Definition critical_dbf_points_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : list Time :=
  0 :: H :: bounded_time_points H ++
  flat_map (fun τ => task_release_points_upto tasks offset τ H) enumT ++
  flat_map (fun τ => task_deadline_points_upto tasks offset τ H) enumT.

Definition critical_dbf_windows_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (H : Time) : list (Time * Time) :=
  let points := critical_dbf_points_upto tasks offset enumT H in
  flat_map
    (fun t1 =>
       map (fun t2 => (t1, t2))
           (filter (fun t2 => (t1 <=? t2) && (t2 <=? H)) points))
    points.

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
    (fun w =>
       let '(t1, t2) := w in
       taskset_periodic_dbf_window tasks offset enumT t1 t2 <=? t2 - t1)
    (critical_dbf_windows_upto tasks offset enumT H).

Record PeriodicEDFConcreteWindowObligations
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H) : Prop := {
  periodic_edf_concrete_tasks_wf :
    well_formed_periodic_tasks_on T tasks;
  periodic_edf_concrete_enumT_nodup :
    NoDup enumT;
  periodic_edf_concrete_enumT_complete :
    forall τ, T τ -> In τ enumT;
  periodic_edf_concrete_enumT_sound :
    forall τ, In τ enumT -> T τ;
  periodic_edf_concrete_deadline_and_no_carry_in :
    forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      job_abs_deadline (jobs j) <= H /\
      periodic_edf_busy_prefix_no_carry_in_bridge
        T tasks offset jobs H
        (generated_periodic_edf_schedule_on_finite_horizon
           T tasks offset jobs H enumT codec)
        j;
  periodic_edf_concrete_window_dbf_test :
    window_dbf_test_upto tasks offset enumT H = true
}.

Lemma critical_dbf_points_upto_complete :
  forall tasks offset enumT H t,
    t <= H ->
    In t (critical_dbf_points_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H t Hle.
  unfold critical_dbf_points_upto.
  simpl.
  destruct t as [|t'].
  - now left.
  - right.
    right.
    right.
    apply in_or_app.
    left.
    unfold bounded_time_points.
    rewrite in_seq.
    lia.
Qed.

Lemma task_release_points_upto_contains_index :
  forall tasks offset τ H k,
    k <= H ->
    expected_release tasks offset τ k <= H ->
    In (expected_release tasks offset τ k)
       (task_release_points_upto tasks offset τ H).
Proof.
  intros tasks offset τ H k Hkle Hrel.
  unfold task_release_points_upto.
  apply filter_In.
  split.
  - apply in_map_iff.
    exists k.
    split; [reflexivity|].
    unfold bounded_time_points.
    rewrite in_seq.
    lia.
  - apply Nat.leb_le.
    exact Hrel.
Qed.

Lemma task_deadline_points_upto_contains_index :
  forall tasks offset τ H k,
    k <= H ->
    expected_abs_deadline tasks offset τ k <= H ->
    In (expected_abs_deadline tasks offset τ k)
       (task_deadline_points_upto tasks offset τ H).
Proof.
  intros tasks offset τ H k Hkle Hdl.
  unfold task_deadline_points_upto.
  apply filter_In.
  split.
  - apply in_map_iff.
    exists k.
    split; [reflexivity|].
    + unfold bounded_time_points.
      rewrite in_seq.
      lia.
  - apply Nat.leb_le.
    exact Hdl.
Qed.

Lemma critical_dbf_points_upto_contains_release :
  forall tasks offset enumT H τ k,
    In τ enumT ->
    k <= H ->
    expected_release tasks offset τ k <= H ->
    In (expected_release tasks offset τ k)
       (critical_dbf_points_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H τ k Hinτ Hkle Hrel.
  unfold critical_dbf_points_upto.
  simpl.
  right.
  right.
  right.
  apply in_or_app.
  right.
  apply in_or_app.
  left.
  apply in_flat_map.
  exists τ.
  split; [exact Hinτ|].
  apply task_release_points_upto_contains_index; assumption.
Qed.

Lemma critical_dbf_points_upto_contains_deadline :
  forall tasks offset enumT H τ k,
    In τ enumT ->
    k <= H ->
    expected_abs_deadline tasks offset τ k <= H ->
    In (expected_abs_deadline tasks offset τ k)
       (critical_dbf_points_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H τ k Hinτ Hkle Hdl.
  unfold critical_dbf_points_upto.
  simpl.
  right.
  right.
  right.
  apply in_or_app.
  right.
  apply in_or_app.
  right.
  apply in_flat_map.
  exists τ.
  split; [exact Hinτ|].
  apply task_deadline_points_upto_contains_index; assumption.
Qed.

Lemma critical_dbf_windows_upto_complete :
  forall tasks offset enumT H t1 t2,
    t1 <= t2 ->
    t2 <= H ->
    In (t1, t2) (critical_dbf_windows_upto tasks offset enumT H).
Proof.
  intros tasks offset enumT H t1 t2 Hle12 Hle2H.
  unfold critical_dbf_windows_upto.
  apply in_flat_map.
  exists t1.
  split.
  - apply critical_dbf_points_upto_complete. lia.
  - apply in_map_iff.
    exists t2.
    split; [reflexivity|].
    apply filter_In.
    split.
    + apply critical_dbf_points_upto_complete. exact Hle2H.
    + rewrite andb_true_iff.
      rewrite !Nat.leb_le.
      lia.
Qed.

Lemma critical_dbf_windows_upto_bounds :
  forall tasks offset enumT H t1 t2,
    In (t1, t2) (critical_dbf_windows_upto tasks offset enumT H) ->
    t1 <= t2 /\ t2 <= H.
Proof.
  intros tasks offset enumT H t1 t2 Hin.
  unfold critical_dbf_windows_upto in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [x [Hin_points Hin_pairs]].
  apply in_map_iff in Hin_pairs.
  destruct Hin_pairs as [t2' [Hpair Hin_filter]].
  inversion Hpair; subst x t2'; clear Hpair.
  apply filter_In in Hin_filter.
  destruct Hin_filter as [_ Hbounds].
  rewrite andb_true_iff in Hbounds.
  rewrite !Nat.leb_le in Hbounds.
  exact Hbounds.
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

Lemma critical_dbf_windows_upto_sound :
  forall tasks offset enumT H t1 t2,
    window_dbf_test_upto tasks offset enumT H = true ->
    In (t1, t2) (critical_dbf_windows_upto tasks offset enumT H) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks offset enumT H t1 t2 Htest Hin.
  unfold window_dbf_test_upto in Htest.
  apply forallb_forall with (x := (t1, t2)) in Htest; auto.
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
  eapply critical_dbf_windows_upto_sound; eauto.
  apply critical_dbf_windows_upto_complete; assumption.
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

Definition zero_offset_window_dbf_cutoff_bound
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : Time :=
  scalar_dbf_cutoff_bound tasks enumT.

Definition window_dbf_test_by_cutoff
    (tasks : TaskId -> Task)
    (enumT : list TaskId) : bool :=
  window_dbf_test_upto tasks (fun _ => 0) enumT
                       (zero_offset_window_dbf_cutoff_bound tasks enumT)
  && dbf_test_by_cutoff tasks enumT.

Record PeriodicEDFConcreteClassicalObligations
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicFiniteHorizonCodec T tasks (fun _ => 0) jobs H) : Prop := {
  periodic_edf_concrete_window_base :
    PeriodicEDFConcreteWindowObligations
      T tasks (fun _ => 0) jobs H enumT codec;
  periodic_edf_concrete_dbf_test_by_cutoff :
    dbf_test_by_cutoff tasks enumT = true
}.

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

Theorem window_dbf_test_by_cutoff_sound :
  forall tasks enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    window_dbf_test_by_cutoff tasks enumT = true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks (fun _ => 0) enumT t1 t2 <= t2 - t1.
Proof.
  intros tasks enumT Hnodup Hpos Htest t1 t2 Hle.
  apply andb_true_iff in Htest.
  destruct Htest as [_ Hscalar].
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. reflexivity.
    + exact Hpos.
  - apply (dbf_check_by_cutoff tasks enumT Hnodup Hpos).
    exact Hscalar.
Qed.

Theorem window_dbf_check_by_cutoff :
  forall tasks enumT,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    window_dbf_test_by_cutoff tasks enumT = true ->
    forall t1 t2,
      t1 <= t2 ->
      taskset_periodic_dbf_window tasks (fun _ => 0) enumT t1 t2 <= t2 - t1.
Proof.
  exact window_dbf_test_by_cutoff_sound.
Qed.
