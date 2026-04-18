From Stdlib Require Import Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.PlacementFacts.

(** Abstract migration between two consecutive slots. *)
Definition migrates_between
    (sched : Schedule) (j : JobId) (t : Time) (c1 c2 : CPU) : Prop :=
  c1 <> c2 /\
  sched t c1 = Some j /\
  sched (S t) c2 = Some j.

Lemma migration_respects_admissibility :
  forall adm m sched j t c1 c2,
    schedule_respects_admissibility adm m sched ->
    c1 < m ->
    c2 < m ->
    migrates_between sched j t c1 c2 ->
    adm j c1 /\ adm j c2.
Proof.
  intros adm m sched j t c1 c2 Hrespect Hc1 Hc2 [_ [Hrun1 Hrun2]].
  split.
  - eapply running_on_admissible_cpu; eauto.
  - eapply running_on_admissible_cpu; eauto.
Qed.

Lemma singleton_respect_prevents_cross_cpu_migration :
  forall assign m sched j t c1 c2,
    schedule_respects_admissibility (singleton_admissibility assign) m sched ->
    c1 < m ->
    c2 < m ->
    sched t c1 = Some j ->
    sched (S t) c2 = Some j ->
    c1 = c2.
Proof.
  intros assign m sched j t c1 c2 Hrespect Hc1 Hc2 Hrun1 Hrun2.
  pose proof
    (singleton_schedule_respects_implies_assigned_cpu
       assign m sched j t c1 Hrespect Hc1 Hrun1) as Hass1.
  pose proof
    (singleton_schedule_respects_implies_assigned_cpu
       assign m sched j (S t) c2 Hrespect Hc2 Hrun2) as Hass2.
  congruence.
Qed.
