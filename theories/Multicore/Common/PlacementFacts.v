From Stdlib Require Import Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.

(** Placement invariant for multicore schedules:
    every scheduled job runs only on an admissible CPU. *)
Definition schedule_respects_admissibility
    (adm : admissible_cpu) (m : nat) (sched : Schedule) : Prop :=
  forall j t c,
    c < m ->
    sched t c = Some j ->
    adm j c.

Lemma running_on_admissible_cpu :
  forall adm m sched j t c,
    schedule_respects_admissibility adm m sched ->
    c < m ->
    sched t c = Some j ->
    adm j c.
Proof.
  intros adm m sched j t c Hrespect Hlt Hrun.
  exact (Hrespect j t c Hlt Hrun).
Qed.

Lemma running_implies_admissible_somewhere_under_respect :
  forall adm jobs m sched j t,
    valid_schedule jobs m sched ->
    schedule_respects_admissibility adm m sched ->
    running m sched j t ->
    admissible_somewhere adm jobs m sched j t.
Proof.
  intros adm jobs m sched j t Hvalid Hrespect [c [Hlt Hrun]].
  exists c.
  unfold admissible_somewhere, eligible_on_cpu, runnable_on_cpu.
  split; [exact Hlt |].
  split.
  - exact (Hrespect j t c Hlt Hrun).
  - exact (Hvalid j t c Hlt Hrun).
Qed.

Lemma all_cpus_schedule_respects_admissibility :
  forall m sched,
    schedule_respects_admissibility all_cpus_admissible m sched.
Proof.
  intros m sched j t c _ _.
  exact I.
Qed.

Lemma singleton_schedule_respects_implies_assigned_cpu :
  forall assign m sched j t c,
    schedule_respects_admissibility (singleton_admissibility assign) m sched ->
    c < m ->
    sched t c = Some j ->
    assign j = c.
Proof.
  intros assign m sched j t c Hrespect Hlt Hrun.
  exact (Hrespect j t c Hlt Hrun).
Qed.
