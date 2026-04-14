(* This file collects multicore-generic notions that are independent of
   partitioned/global policy choice.

   Scope:
   - per-CPU view of a global schedule
   - no-duplication / idle / busy / runnable-like notions
   - light bridge lemmas to Schedule / ScheduleFacts

   Follow-on theorem layers:
   - ServiceFacts.v      (migration-aware service decomposition)
   - CompletionFacts.v   (completion/service bridge on multicore schedules)

   Non-goals of this file:
   - assignment-specific partitioned reasoning
   - top-m global choose
   - work-conserving definitions tied to a specific admissibility model
   - operational / refinement semantics
 *)

(* Fully constructive: no Classical import. *)

From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.

(* ===== Multicore common definitions ===== *)

(* Global schedule restricted to CPU c, seen as a 1-CPU schedule on virtual CPU 0. *)
Definition cpu_schedule (sched : Schedule) (c : CPU) : Schedule :=
  fun t cpu' => if Nat.eqb cpu' 0 then sched t c else None.

(* Preferred multicore name; keep compatibility with existing ScheduleModel. *)
Definition no_duplication (m : nat) (sched : Schedule) : Prop :=
  sequential_jobs m sched.

Definition cpu_idle (sched : Schedule) (t : Time) (c : CPU) : Prop :=
  sched t c = None.

Definition cpu_busy (sched : Schedule) (t : Time) (c : CPU) : Prop :=
  exists j, sched t c = Some j.

Definition all_cpus_idle (m : nat) (sched : Schedule) (t : Time) : Prop :=
  forall c, c < m -> cpu_idle sched t c.

Definition some_cpu_idle (m : nat) (sched : Schedule) (t : Time) : Prop :=
  exists c, c < m /\ cpu_idle sched t c.

Definition globally_runnable
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time) : Prop :=
  exists j, eligible jobs m sched j t.

(* Optional forward-compatible hook for affinity/global WC later. *)
Definition admissible_cpu := JobId -> CPU -> Prop.

Definition runnable_on_cpu
    (adm : admissible_cpu)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) (c : CPU) : Prop :=
  c < m /\ adm j c /\ eligible jobs m sched j t.

(* ===== A. cpu_schedule basic lemmas ===== *)

Lemma cpu_schedule_eq_cpu0 :
  forall sched c t,
    cpu_schedule sched c t 0 = sched t c.
Proof.
  intros sched c t.
  unfold cpu_schedule.
  simpl.
  reflexivity.
Qed.

Lemma cpu_schedule_idle_other_cpus :
  forall sched c t cpu',
    0 < cpu' ->
    cpu_schedule sched c t cpu' = None.
Proof.
  intros sched c t cpu' Hlt.
  unfold cpu_schedule.
  destruct (Nat.eqb cpu' 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - reflexivity.
Qed.

Lemma runs_on_cpu_schedule :
  forall sched c j t,
    runs_on (cpu_schedule sched c) j t 0 = runs_on sched j t c.
Proof.
  intros sched c j t.
  unfold runs_on, cpu_schedule. simpl. reflexivity.
Qed.

Lemma running_on_cpu_schedule_iff :
  forall sched c j t,
    running 1 (cpu_schedule sched c) j t <-> sched t c = Some j.
Proof.
  intros sched c j t.
  unfold running.
  split.
  - intros [c' [Hlt Hsome]].
    assert (c' = 0) by lia. subst c'.
    unfold cpu_schedule in Hsome.
    simpl in Hsome. exact Hsome.
  - intros Hsome.
    exists 0. split.
    + lia.
    + unfold cpu_schedule. simpl. exact Hsome.
Qed.

(* ===== B. no_duplication bridge lemma ===== *)

Lemma no_duplication_iff_sequential_jobs :
  forall m sched,
    no_duplication m sched <-> sequential_jobs m sched.
Proof.
  intros m sched.
  unfold no_duplication.
  tauto.
Qed.

(* ===== C. cpu_count bridge lemmas ===== *)

Lemma no_duplication_cpu_count_le_1 :
  forall m sched j t,
    no_duplication m sched ->
    cpu_count m sched j t <= 1.
Proof.
  intros m sched j t Hnd.
  apply cpu_count_le_1.
  exact Hnd.
Qed.

Lemma no_duplication_cpu_count_0_or_1 :
  forall m sched j t,
    no_duplication m sched ->
    cpu_count m sched j t = 0 \/ cpu_count m sched j t = 1.
Proof.
  intros m sched j t Hnd.
  apply cpu_count_0_or_1.
  exact Hnd.
Qed.

Lemma no_duplication_cpu_count_eq_1_iff_executed :
  forall m sched j t,
    no_duplication m sched ->
    (cpu_count m sched j t = 1 <->
     exists c, c < m /\ sched t c = Some j).
Proof.
  intros m sched j t Hnd.
  apply cpu_count_eq_1_iff_executed.
  exact Hnd.
Qed.

(* ===== D. idle / busy lemmas ===== *)

Lemma cpu_idle_iff_not_busy :
  forall sched t c,
    cpu_idle sched t c <-> ~ cpu_busy sched t c.
Proof.
  intros sched t c.
  unfold cpu_idle, cpu_busy.
  split.
  - intros Hnone [j Hsome].
    rewrite Hnone in Hsome. discriminate.
  - intros Hnot.
    destruct (sched t c) as [j|] eqn:E.
    + exfalso. apply Hnot. exists j. reflexivity.
    + reflexivity.
Qed.

Lemma all_cpus_idle_implies_not_running :
  forall m sched j t,
    all_cpus_idle m sched t ->
    ~ running m sched j t.
Proof.
  intros m sched j t Hidle [c [Hlt Hsome]].
  unfold all_cpus_idle, cpu_idle in Hidle.
  pose proof (Hidle c Hlt) as Hnone.
  rewrite Hnone in Hsome. discriminate.
Qed.

(* ===== E. validity / runnable connection lemmas ===== *)

Lemma valid_running_implies_globally_runnable :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    running m sched j t ->
    globally_runnable jobs m sched t.
Proof.
  intros jobs m sched j t Hvalid [c [Hlt Hsome]].
  unfold globally_runnable.
  exists j.
  exact (Hvalid j t c Hlt Hsome).
Qed.

Lemma eligible_implies_globally_runnable :
  forall jobs m sched j t,
    eligible jobs m sched j t ->
    globally_runnable jobs m sched t.
Proof.
  intros jobs m sched j t Helig.
  unfold globally_runnable.
  exists j. exact Helig.
Qed.
