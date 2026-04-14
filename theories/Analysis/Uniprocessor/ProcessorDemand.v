From Stdlib Require Import Arith Arith.PeanoNat Lia List Sorting.Permutation.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.
From RocqSched Require Import Analysis.Uniprocessor.BusyWindowSearch.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.

Import ListNotations.

Fixpoint taskset_periodic_dbf
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : nat :=
  match enumT with
  | [] => 0
  | τ :: enumT' =>
      periodic_dbf tasks τ H + taskset_periodic_dbf tasks enumT' H
  end.

Definition taskset_sporadic_dbf_bound
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : nat :=
  taskset_periodic_dbf tasks enumT H.

Definition taskset_jittered_periodic_dbf_bound
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (H : Time) : nat :=
  taskset_periodic_dbf tasks enumT H.

Lemma taskset_sporadic_dbf_bound_eq_periodic :
  forall tasks enumT H,
    taskset_sporadic_dbf_bound tasks enumT H =
    taskset_periodic_dbf tasks enumT H.
Proof. reflexivity. Qed.

Lemma taskset_jittered_periodic_dbf_bound_eq_sporadic :
  forall tasks enumT H,
    taskset_jittered_periodic_dbf_bound tasks enumT H =
    taskset_sporadic_dbf_bound tasks enumT H.
Proof. reflexivity. Qed.

Lemma taskset_periodic_dbf_monotone :
  forall tasks enumT H1 H2,
    H1 <= H2 ->
    taskset_periodic_dbf tasks enumT H1 <= taskset_periodic_dbf tasks enumT H2.
Proof.
  intros tasks enumT H1 H2 Hle.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - apply Nat.add_le_mono.
    + apply periodic_dbf_monotone. exact Hle.
    + exact IH.
Qed.

Lemma taskset_sporadic_dbf_bound_monotone :
  forall tasks enumT H1 H2,
    H1 <= H2 ->
    taskset_sporadic_dbf_bound tasks enumT H1 <=
    taskset_sporadic_dbf_bound tasks enumT H2.
Proof.
  intros tasks enumT H1 H2 Hle.
  unfold taskset_sporadic_dbf_bound.
  exact (taskset_periodic_dbf_monotone tasks enumT H1 H2 Hle).
Qed.

Lemma taskset_jittered_periodic_dbf_bound_monotone :
  forall tasks enumT H1 H2,
    H1 <= H2 ->
    taskset_jittered_periodic_dbf_bound tasks enumT H1 <=
    taskset_jittered_periodic_dbf_bound tasks enumT H2.
Proof.
  intros tasks enumT H1 H2 Hle.
  unfold taskset_jittered_periodic_dbf_bound.
  exact (taskset_periodic_dbf_monotone tasks enumT H1 H2 Hle).
Qed.

Lemma taskset_periodic_dbf_app :
  forall tasks enumT1 enumT2 H,
    taskset_periodic_dbf tasks (enumT1 ++ enumT2) H =
    taskset_periodic_dbf tasks enumT1 H +
    taskset_periodic_dbf tasks enumT2 H.
Proof.
  intros tasks enumT1 enumT2 H.
  induction enumT1 as [|τ enumT1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma taskset_sporadic_dbf_bound_app :
  forall tasks enumT1 enumT2 H,
    taskset_sporadic_dbf_bound tasks (enumT1 ++ enumT2) H =
    taskset_sporadic_dbf_bound tasks enumT1 H +
    taskset_sporadic_dbf_bound tasks enumT2 H.
Proof.
  intros tasks enumT1 enumT2 H.
  unfold taskset_sporadic_dbf_bound.
  apply taskset_periodic_dbf_app.
Qed.

Lemma taskset_jittered_periodic_dbf_bound_app :
  forall tasks enumT1 enumT2 H,
    taskset_jittered_periodic_dbf_bound tasks (enumT1 ++ enumT2) H =
    taskset_jittered_periodic_dbf_bound tasks enumT1 H +
    taskset_jittered_periodic_dbf_bound tasks enumT2 H.
Proof.
  intros tasks enumT1 enumT2 H.
  unfold taskset_jittered_periodic_dbf_bound.
  apply taskset_periodic_dbf_app.
Qed.

Lemma taskset_periodic_dbf_remove_head :
  forall tasks τ enumT H,
    ~ In τ enumT ->
    taskset_periodic_dbf tasks (τ :: enumT) H =
    taskset_periodic_dbf tasks enumT H + periodic_dbf tasks τ H.
Proof.
  intros tasks τ enumT H _.
  simpl. lia.
Qed.

Lemma taskset_periodic_dbf_perm :
  forall tasks enumT1 enumT2 H,
    Permutation enumT1 enumT2 ->
    taskset_periodic_dbf tasks enumT1 H =
    taskset_periodic_dbf tasks enumT2 H.
Proof.
  intros tasks enumT1 enumT2 H Hperm.
  induction Hperm; simpl; try lia.
Qed.

Lemma taskset_periodic_dbf_nodup_stable :
  forall tasks enumT1 enumT2 H,
    NoDup enumT1 ->
    NoDup enumT2 ->
    (forall τ, In τ enumT1 <-> In τ enumT2) ->
    taskset_periodic_dbf tasks enumT1 H =
    taskset_periodic_dbf tasks enumT2 H.
Proof.
  intros tasks enumT1 enumT2 H Hnd1 Hnd2 Hequiv.
  apply taskset_periodic_dbf_perm.
  eapply NoDup_Permutation; eauto.
Qed.

Lemma busy_interval_cpu_supply_eq_length :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    cpu_service_between sched t1 t2 = t2 - t1.
Proof.
  exact cpu_service_between_busy_interval_eq_length.
Qed.

Lemma demand_exceeds_supply_implies_lt :
  forall supply demand,
    supply < demand ->
    supply <= demand.
Proof.
  intros supply demand Hlt. lia.
Qed.

Lemma demand_exceeds_busy_interval_length_contradiction :
  forall sched t1 t2 demand,
    busy_interval sched t1 t2 ->
    t2 - t1 < demand ->
    cpu_service_between sched t1 t2 < demand.
Proof.
  intros sched t1 t2 demand Hbusy Hlt.
  rewrite busy_interval_cpu_supply_eq_length by exact Hbusy.
  exact Hlt.
Qed.

Definition periodic_processor_demand_witness
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (sched : Schedule)
    (t1 t2 : Time) : Prop :=
  busy_window_candidate sched t1 t2 /\
  cpu_service_between sched t1 t2 <
  taskset_periodic_dbf tasks enumT (t2 - t1).

Definition sporadic_processor_demand_witness
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (sched : Schedule)
    (t1 t2 : Time) : Prop :=
  busy_window_candidate sched t1 t2 /\
  cpu_service_between sched t1 t2 <
  taskset_sporadic_dbf_bound tasks enumT (t2 - t1).

Definition jittered_periodic_processor_demand_witness
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (sched : Schedule)
    (t1 t2 : Time) : Prop :=
  busy_window_candidate sched t1 t2 /\
  cpu_service_between sched t1 t2 <
  taskset_jittered_periodic_dbf_bound tasks enumT (t2 - t1).

Lemma taskset_periodic_dbf_exceeds_busy_window_supply :
  forall tasks enumT sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    t2 - t1 < taskset_periodic_dbf tasks enumT (t2 - t1) ->
    periodic_processor_demand_witness tasks enumT sched t1 t2.
Proof.
  intros tasks enumT sched t1 t2 Hbusy Hover.
  split; [exact Hbusy |].
  rewrite busy_window_candidate_cpu_supply_eq_length by exact Hbusy.
  exact Hover.
Qed.

Lemma taskset_sporadic_dbf_exceeds_busy_window_supply :
  forall tasks enumT sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    t2 - t1 < taskset_sporadic_dbf_bound tasks enumT (t2 - t1) ->
    sporadic_processor_demand_witness tasks enumT sched t1 t2.
Proof.
  intros tasks enumT sched t1 t2 Hbusy Hover.
  split; [exact Hbusy |].
  rewrite taskset_sporadic_dbf_bound_eq_periodic in Hover.
  rewrite busy_window_candidate_cpu_supply_eq_length by exact Hbusy.
  exact Hover.
Qed.

Lemma taskset_jittered_periodic_dbf_exceeds_busy_window_supply :
  forall tasks enumT sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    t2 - t1 < taskset_jittered_periodic_dbf_bound tasks enumT (t2 - t1) ->
    jittered_periodic_processor_demand_witness tasks enumT sched t1 t2.
Proof.
  intros tasks enumT sched t1 t2 Hbusy Hover.
  split; [exact Hbusy |].
  rewrite taskset_jittered_periodic_dbf_bound_eq_sporadic in Hover.
  rewrite taskset_sporadic_dbf_bound_eq_periodic in Hover.
  rewrite busy_window_candidate_cpu_supply_eq_length by exact Hbusy.
  exact Hover.
Qed.
