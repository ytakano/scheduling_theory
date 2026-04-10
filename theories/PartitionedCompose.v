From Stdlib Require Import Arith Arith.PeanoNat Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import Partitioned.

(* Fully constructive: no Classical import. *)

(** * Partitioned Schedule Composition Layer

    This file provides the generic machinery to combine per-CPU single-CPU
    witness schedules into one global partitioned schedule, and to lift local
    schedulability witnesses to global [schedulable_by_on J].

    The key definition is [glue_local_schedules]: for each CPU c < m, it
    reads the job assigned to virtual CPU 0 in the local schedule [locals c].
    CPUs c >= m are always idle.

    The main theorems are:
    - [glue_local_rels_imply_partitioned_schedule_on]: local dispatch rels →
      [raw_partitioned_schedule_on] for the glued schedule.
    - [local_witnesses_imply_partitioned_schedulable_by_on]: the canonical
      entry point — give per-CPU (rel, feasibility) witnesses and obtain
      [schedulable_by_on J] for the partitioned scheduler.               *)

(* ===== Definition: glue_local_schedules ===== *)

(** Combine per-CPU single-CPU schedules into one global m-CPU schedule.
    For CPU c < m, the global schedule at (t, c) is whatever the local
    schedule [locals c] runs on its virtual CPU 0 at time t.
    CPUs c >= m are always idle. *)
Definition glue_local_schedules
    (m : nat)
    (locals : CPU -> Schedule) : Schedule :=
  fun t c =>
    if c <? m then locals c t 0 else None.

(* ===== Lemma: cpu_schedule_glue_eq ===== *)

(** If c < m and [locals c] is idle on all virtual CPUs > 0, then the
    single-CPU view of the glued schedule at CPU c equals [locals c]. *)
Lemma cpu_schedule_glue_eq :
    forall m (locals : CPU -> Schedule) c,
      c < m ->
      (forall t cpu', 0 < cpu' -> locals c t cpu' = None) ->
      cpu_schedule (glue_local_schedules m locals) c = locals c.
Proof.
  intros m locals c Hc Hidle.
  extensionality t.
  extensionality cpu'.
  unfold cpu_schedule, glue_local_schedules.
  destruct (Nat.eqb cpu' 0) eqn:E0.
  - apply Nat.eqb_eq in E0. subst cpu'.
    apply Nat.ltb_lt in Hc.
    rewrite Hc.
    reflexivity.
  - apply Nat.eqb_neq in E0.
    symmetry.
    apply Hidle.
    lia.
Qed.

(* ===== Helper: extract idle condition from scheduler_rel ===== *)

(** Extract the "locals c is idle on virtual CPUs > 0" condition from a
    single-CPU dispatch scheduler_rel hypothesis. *)
Lemma scheduler_rel_single_cpu_idle :
    forall spec cands jobs (sched : Schedule) t cpu',
      scheduler_rel (single_cpu_dispatch_schedule spec cands) jobs 1 sched ->
      0 < cpu' ->
      sched t cpu' = None.
Proof.
  intros spec cands jobs sched t cpu' [_ Hsteps] Hlt.
  exact (proj2 (Hsteps t) cpu' Hlt).
Qed.

(* ===== Theorem: glue_local_rels_imply_partitioned_schedule_on ===== *)

(** Main composition theorem: if each CPU c < m satisfies the local
    single-CPU dispatch relation, then [glue_local_schedules m locals]
    satisfies [raw_partitioned_schedule_on]. *)
Theorem glue_local_rels_imply_partitioned_schedule_on :
    forall m spec (cands : CPU -> CandidateSource)
           jobs (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_dispatch_schedule spec (cands c))
          jobs 1 (locals c)) ->
      raw_partitioned_schedule_on m spec cands jobs
        (glue_local_schedules m locals).
Proof.
  intros m spec cands jobs locals Hlocals.
  apply (proj2 (partitioned_schedule_on_iff_local_rel m spec cands jobs
                  (glue_local_schedules m locals))).
  intros c Hlt.
  pose proof (Hlocals c Hlt) as Hrel.
  rewrite (cpu_schedule_glue_eq m locals c Hlt).
  - exact Hrel.
  - intros t cpu' Hcpu'.
    exact (scheduler_rel_single_cpu_idle spec (cands c) jobs (locals c) t cpu'
             Hrel Hcpu').
Qed.

(* ===== Theorem: local_witnesses_imply_partitioned_schedulable_by_on ===== *)

(** Standard entry point for partitioned schedulability from explicit per-CPU
    witness schedules.

    Given:
    - A static CPU assignment [assign] with [valid_assignment]
    - A dispatch policy [spec] with per-CPU candidate sources [cands]
    - Proof that [cands c] satisfies [CandidateSourceSpec] for each c < m
    - Per-CPU witness schedules [locals c] each satisfying:
        (a) the local dispatch scheduler_rel, and
        (b) feasibility on the local job set

    Conclude: [schedulable_by_on J (partitioned_scheduler m spec cands) jobs m]. *)
Theorem local_witnesses_imply_partitioned_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericDispatchSpec)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_dispatch_schedule spec (cands c))
          jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs locals Hlocals.
  set (sched := glue_local_schedules m locals).
  apply (partitioned_schedulable_by_on_from_local
           assign m valid_assignment spec J cands cands_spec jobs sched).
  - apply valid_partitioned_schedule_intro.
    apply glue_local_rels_imply_partitioned_schedule_on.
    intros c Hlt.
    exact (proj1 (Hlocals c Hlt)).
  - intros c Hlt.
    pose proof (Hlocals c Hlt) as [Hrel Hfeas].
    unfold sched.
    rewrite (cpu_schedule_glue_eq m locals c Hlt).
    + exact Hfeas.
    + intros t cpu' Hcpu'.
      exact (scheduler_rel_single_cpu_idle spec (cands c) jobs (locals c) t cpu'
               Hrel Hcpu').
Qed.
