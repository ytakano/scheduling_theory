(* Admissibility.v
   CPU-job admissibility predicates built on top of MultiCoreBase.

   This file enriches the minimal `admissible_cpu` / `runnable_on_cpu` stubs
   that already live in MultiCoreBase with concrete instances and bridge lemmas.

   New definitions
   ---------------
   - eligible_on_cpu    : transparent alias for runnable_on_cpu
   - all_cpus_admissible
   - singleton_admissibility
   - ready_on_cpu
   - admissible_somewhere

   Lemmas
   ------
   - eligible_on_cpu_implies_eligible
   - eligible_on_cpu_implies_globally_runnable
   - singleton_admissibility_cpu
   - singleton_admissibility_unique
   - local_jobset_iff_singleton_admissibility   (bridge to Partitioned.v)
*)

From Stdlib Require Import Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Multicore.Common.MultiCoreBase.

(* ===== Concrete admissibility instances ===== *)

(** Every job is admissible on every CPU. *)
Definition all_cpus_admissible : admissible_cpu :=
  fun _ _ => True.

(** Each job is admissible on exactly the one CPU it is assigned to. *)
Definition singleton_admissibility
    (assign : JobId -> CPU) : admissible_cpu :=
  fun j c => assign j = c.

(* ===== eligible_on_cpu (alias for runnable_on_cpu) ===== *)

(** Transparent alias. `runnable_on_cpu` already captures exactly this
    concept; we expose a second name for readability at call sites that
    discuss eligibility rather than runnability. *)
Definition eligible_on_cpu
    (adm : admissible_cpu)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) (c : CPU) : Prop :=
  runnable_on_cpu adm jobs m sched j t c.

(** A job is ready on a specific CPU when it is eligible there and not
    currently running anywhere. *)
Definition ready_on_cpu
    (adm : admissible_cpu)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) (c : CPU) : Prop :=
  eligible_on_cpu adm jobs m sched j t c /\ ~ running m sched j t.

(** A job is admissible somewhere when there exists at least one CPU on
    which it is eligible. *)
Definition admissible_somewhere
    (adm : admissible_cpu)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  exists c, eligible_on_cpu adm jobs m sched j t c.

(* ===== Lemmas ===== *)

Lemma eligible_on_cpu_implies_eligible :
  forall adm jobs m sched j t c,
    eligible_on_cpu adm jobs m sched j t c ->
    eligible jobs m sched j t.
Proof.
  intros adm jobs m sched j t c H.
  unfold eligible_on_cpu, runnable_on_cpu in H.
  tauto.
Qed.

Lemma eligible_on_cpu_implies_globally_runnable :
  forall adm jobs m sched j t c,
    eligible_on_cpu adm jobs m sched j t c ->
    globally_runnable jobs m sched t.
Proof.
  intros adm jobs m sched j t c H.
  apply eligible_implies_globally_runnable with j.
  exact (eligible_on_cpu_implies_eligible adm jobs m sched j t c H).
Qed.

Lemma all_cpus_admissible_eligible_on_cpu_iff :
  forall jobs m sched j t c,
    c < m ->
    (eligible_on_cpu all_cpus_admissible jobs m sched j t c <->
     eligible jobs m sched j t).
Proof.
  intros jobs m sched j t c Hlt.
  unfold eligible_on_cpu, runnable_on_cpu, all_cpus_admissible.
  split.
  - intros [_ [_ Helig]]. exact Helig.
  - intros Helig. split; [exact Hlt |]. split; [exact I | exact Helig].
Qed.

Lemma admissible_somewhere_of_all_cpus_admissible :
  forall jobs m sched j t,
    0 < m ->
    eligible jobs m sched j t ->
    admissible_somewhere all_cpus_admissible jobs m sched j t.
Proof.
  intros jobs m sched j t Hm Helig.
  exists 0.
  apply (proj2 (all_cpus_admissible_eligible_on_cpu_iff jobs m sched j t 0 Hm)).
  exact Helig.
Qed.

Lemma ready_on_cpu_implies_not_running :
  forall adm jobs m sched j t c,
    ready_on_cpu adm jobs m sched j t c ->
    ~ running m sched j t.
Proof.
  intros adm jobs m sched j t c Hready.
  exact (proj2 Hready).
Qed.

Lemma admissible_somewhere_implies_eligible :
  forall adm jobs m sched j t,
    admissible_somewhere adm jobs m sched j t ->
    eligible jobs m sched j t.
Proof.
  intros adm jobs m sched j t [c Helig].
  exact (eligible_on_cpu_implies_eligible adm jobs m sched j t c Helig).
Qed.

Lemma singleton_admissibility_cpu :
  forall (assign : JobId -> CPU) j c,
    singleton_admissibility assign j c <-> assign j = c.
Proof.
  intros assign j c.
  unfold singleton_admissibility.
  tauto.
Qed.

Lemma singleton_admissibility_unique :
  forall (assign : JobId -> CPU) j c1 c2,
    singleton_admissibility assign j c1 ->
    singleton_admissibility assign j c2 ->
    c1 = c2.
Proof.
  intros assign j c1 c2 H1 H2.
  unfold singleton_admissibility in *.
  congruence.
Qed.

(** Bridge lemma: the `local_jobset` predicate used in Partitioned.v is
    equivalent to membership combined with singleton admissibility. *)
Lemma local_jobset_iff_singleton_admissibility :
  forall (assign : JobId -> CPU) (J : JobId -> Prop) c j,
    (J j /\ singleton_admissibility assign j c) <-> (J j /\ assign j = c).
Proof.
  intros assign J c j.
  unfold singleton_admissibility.
  tauto.
Qed.
