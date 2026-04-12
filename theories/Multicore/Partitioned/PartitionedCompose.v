From Stdlib Require Import Arith Arith.PeanoNat Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From SchedulingTheory Require Import Multicore.Common.MultiCoreBase.
From SchedulingTheory Require Import Multicore.Partitioned.Partitioned.

(* Fully constructive: no Classical import. *)

(** * Partitioned Schedule Composition Layer

    This file provides the generic machinery to combine per-CPU single-CPU
    witness schedules into one global partitioned schedule, and to lift local
    schedulability witnesses to global [schedulable_by_on J].

    The key definition is [glue_local_schedules]: for each CPU c < m, it
    reads the job assigned to virtual CPU 0 in the local schedule [locals c].
    CPUs c >= m are always idle.

    The main theorems are:
    - [glue_local_rels_imply_partitioned_schedule_on]: local choose rels →
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

Corollary glue_cpu_schedule_eq_local :
    forall m (locals : CPU -> Schedule) c,
      c < m ->
      (forall t cpu', 0 < cpu' -> locals c t cpu' = None) ->
      cpu_schedule (glue_local_schedules m locals) c = locals c.
Proof.
  exact cpu_schedule_glue_eq.
Qed.

(* ===== Helper: extract idle condition from scheduler_rel ===== *)

(** Extract the "locals c is idle on virtual CPUs > 0" condition from a
    single-CPU choose scheduler_rel hypothesis. *)
Lemma scheduler_rel_single_cpu_idle :
    forall spec cands jobs (sched : Schedule) t cpu',
      scheduler_rel (single_cpu_algorithm_schedule spec cands) jobs 1 sched ->
      0 < cpu' ->
      sched t cpu' = None.
Proof.
  intros spec cands jobs sched t cpu' [_ Hsteps] Hlt.
  exact (proj2 (Hsteps t) cpu' Hlt).
Qed.

Corollary glue_other_cpus_idle_local_view :
    forall spec cands jobs (sched : Schedule) t cpu',
      scheduler_rel (single_cpu_algorithm_schedule spec cands) jobs 1 sched ->
      0 < cpu' ->
      sched t cpu' = None.
Proof.
  exact scheduler_rel_single_cpu_idle.
Qed.

(* ===== Helper: finite choice over CPUs < m ===== *)

(** Constructively choose one local schedule witness for each CPU c < m. *)
Lemma finite_schedule_choice_lt :
    forall m (P : CPU -> Schedule -> Prop),
      (forall c, c < m -> exists sched, P c sched) ->
      exists locals : CPU -> Schedule,
        forall c, c < m -> P c (locals c).
Proof.
  induction m as [|m IH]; intros P Hex.
  - exists (fun _ _ _ => None).
    intros c Hlt. lia.
  - assert (Hprev : forall c, c < m -> exists sched, P c sched).
    { intros c Hlt. apply Hex. lia. }
    destruct (IH P Hprev) as [locals Hlocals].
    destruct (Hex m (Nat.lt_succ_diag_r m)) as [schedm Hschedm].
    exists (fun c => if Nat.eq_dec c m then schedm else locals c).
    intros c Hlt.
    destruct (Nat.eq_dec c m) as [-> | Hneq].
    + exact Hschedm.
    + apply Hlocals. lia.
Qed.

(* ===== Theorem: glue_local_rels_imply_partitioned_schedule_on ===== *)

(** Main composition theorem: if each CPU c < m satisfies the local
    single-CPU choose relation, then [glue_local_schedules m locals]
    satisfies [raw_partitioned_schedule_on]. *)
Theorem glue_local_rels_imply_partitioned_schedule_on :
    forall m spec (cands : CPU -> CandidateSource)
           jobs (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (cands c))
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

Theorem glue_respects_assignment :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           jobs (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1 (locals c)) ->
      respects_assignment assign m
        (glue_local_schedules m locals).
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs locals Hlocals.
  eapply (partitioned_schedule_implies_respects_assignment
            assign m spec J cands cands_spec jobs).
  exact (glue_local_rels_imply_partitioned_schedule_on
           m spec cands jobs locals Hlocals).
Qed.

Theorem glue_valid_if_local_valid :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1 (locals c)) ->
      valid_partitioned_schedule assign m spec cands jobs
        (glue_local_schedules m locals).
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs locals Hlocals.
  apply (valid_partitioned_schedule_intro assign m spec cands jobs
           (glue_local_schedules m locals)).
  - exact (glue_local_rels_imply_partitioned_schedule_on
             m spec cands jobs locals Hlocals).
  - eapply (glue_respects_assignment
              assign m valid_assignment spec J cands cands_spec jobs locals).
    exact Hlocals.
Qed.

(* ===== Lemma: extract local witnesses from local schedulability ===== *)

(** If each local job set is schedulable on its assigned CPU, then there
    exists a family of local schedules witnessing the scheduler relation
    and local feasibility on every CPU c < m. *)
Lemma local_schedulable_by_on_implies_local_witnesses :
    forall (assign : JobId -> CPU) (m : nat)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (jobs : JobId -> Job),
      (forall c, c < m ->
        schedulable_by_on
          (local_jobset assign J c)
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1) ->
      exists locals : CPU -> Schedule,
        forall c, c < m ->
          scheduler_rel
            (single_cpu_algorithm_schedule spec (cands c))
            jobs 1 (locals c) /\
          feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c).
Proof.
  intros assign m spec J cands jobs Hsched.
  eapply (finite_schedule_choice_lt m
            (fun c sched =>
               scheduler_rel
                 (single_cpu_algorithm_schedule spec (cands c))
                 jobs 1 sched /\
               feasible_schedule_on (local_jobset assign J c) jobs 1 sched)).
  intros c Hlt.
  destruct (Hsched c Hlt) as [sched [Hrel [_ Hfeas]]].
  exists sched.
  split.
  - exact Hrel.
  - exact Hfeas.
Qed.

(* ===== Theorem: local_witnesses_imply_partitioned_schedulable_by_on ===== *)

(** Standard entry point for partitioned schedulability from explicit per-CPU
    witness schedules.

    Given:
    - A static CPU assignment [assign] with [valid_assignment]
    - A choose policy [spec] with per-CPU candidate sources [cands]
    - Proof that [cands c] satisfies [CandidateSourceSpec] for each c < m
    - Per-CPU witness schedules [locals c] each satisfying:
        (a) the local choose scheduler_rel, and
        (b) feasibility on the local job set

    Conclude: [schedulable_by_on J (partitioned_scheduler m spec cands) jobs m]. *)
Theorem local_witnesses_imply_partitioned_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs locals Hlocals.
  set (sched := glue_local_schedules m locals).
  apply (partitioned_schedulable_by_on_from_local
           assign m valid_assignment spec J cands cands_spec jobs sched).
  - pose proof (glue_local_rels_imply_partitioned_schedule_on
                  m spec cands jobs locals
                  (fun c Hlt => proj1 (Hlocals c Hlt))) as Hraw.
    apply (valid_partitioned_schedule_intro assign m spec cands jobs sched Hraw).
    apply (partitioned_schedule_implies_respects_assignment assign m spec J cands cands_spec jobs sched Hraw).
  - intros c Hlt.
    pose proof (Hlocals c Hlt) as [Hrel Hfeas].
    unfold sched.
    rewrite (cpu_schedule_glue_eq m locals c Hlt).
    + exact Hfeas.
    + intros t cpu' Hcpu'.
      exact (scheduler_rel_single_cpu_idle spec (cands c) jobs (locals c) t cpu'
               Hrel Hcpu').
Qed.

Theorem glue_feasible_on_if_local_feasible_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (locals : CPU -> Schedule),
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1 (locals c) /\
        feasible_schedule_on (local_jobset assign J c) jobs 1 (locals c)) ->
      feasible_partitioned_schedule_on assign m spec J cands
        jobs (glue_local_schedules m locals).
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs locals Hlocals.
  split.
  - eapply (glue_valid_if_local_valid
              assign m valid_assignment spec J cands cands_spec jobs locals).
    intros c Hlt.
    exact (proj1 (Hlocals c Hlt)).
  - eapply (Partitioned.glue_feasible_on_if_local_feasible_on
              assign m valid_assignment J jobs (glue_local_schedules m locals)).
    + eapply (glue_respects_assignment
                assign m valid_assignment spec J cands cands_spec jobs locals).
      intros c Hlt.
      exact (proj1 (Hlocals c Hlt)).
    + intros c Hlt.
      pose proof (Hlocals c Hlt) as [Hrel Hfeas].
      rewrite (glue_cpu_schedule_eq_local m locals c Hlt).
      * exact Hfeas.
      * intros t cpu' Hcpu'.
        exact (glue_other_cpus_idle_local_view spec (cands c) jobs (locals c) t cpu'
                 Hrel Hcpu').
Qed.

(* ===== Theorem: local schedulability implies partitioned schedulability ===== *)

(** High-level entry point for partitioned schedulability.

    If every CPU-local job set is schedulable by the corresponding single-CPU
    scheduler, then the whole job set is schedulable by the partitioned global
    scheduler obtained by gluing those local schedulers. *)
Theorem local_schedulable_by_on_implies_partitioned_schedulable_by_on :
    forall (assign : JobId -> CPU) (m : nat)
           (valid_assignment : forall j, assign j < m)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < m ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job),
      (forall c, c < m ->
        schedulable_by_on
          (local_jobset assign J c)
          (single_cpu_algorithm_schedule spec (cands c))
          jobs 1) ->
      schedulable_by_on J (partitioned_scheduler m spec cands) jobs m.
Proof.
  intros assign m valid_assignment spec J cands cands_spec jobs Hlocal.
  destruct (local_schedulable_by_on_implies_local_witnesses
              assign m spec J cands jobs Hlocal) as [locals Hlocals].
  eapply (local_witnesses_imply_partitioned_schedulable_by_on
            assign m valid_assignment spec J cands cands_spec jobs locals).
  exact Hlocals.
Qed.
