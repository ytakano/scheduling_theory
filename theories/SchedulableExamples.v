From Stdlib Require Import Arith Arith.PeanoNat Lia List.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import MultiCoreBase.
Require Import UniPolicies.EDF.
Require Import UniPolicies.FIFO.
Require Import Partitioned.
Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.
Require Import PartitionedCompose.
Require Import PartitionedPolicies.PartitionedEDF.
Import ListNotations.

(**
  SchedulableExamples.v
  =====================
  現行の relation-based scheduler API を concrete scheduler で使う例。

  このファイルでは次を明示する:
  - single-CPU scheduler (`edf_scheduler`, `fifo_scheduler`) に
    candidate source を与える方法
  - `CandidateSourceSpec` と bridge 補題を使って
    `schedulable_by_on` を導く標準パターン
  - `partitioned_scheduler` を直接使った multi-CPU 例

  注意:
  `jobs : JobId -> Job` は全域関数なので、examples では追跡対象を
  `J : JobId -> Prop` で切り出し、`feasible_schedule_on J` を使う。 *)

(* ================================================================= *)
(** ** Single-CPU examples: EDF / FIFO                                *)
(* ================================================================= *)

Definition single_job : Job := mkJob 0 0 0 1 2.

Definition single_jobs (_ : JobId) : Job := single_job.

Definition J_single (j : JobId) : Prop := j = 0.

Definition singleton_candidates : CandidateSource :=
  fun _jobs _m _sched _t => [0].

Definition single_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    if Nat.eqb t 0 then Some 0 else None
  else None.

Lemma singleton_candidates_spec :
    CandidateSourceSpec J_single singleton_candidates.
Proof.
  refine (mkCandidateSourceSpec J_single singleton_candidates _ _ _).
  - intros jobs m sched t j Hin.
    simpl in Hin.
    destruct Hin as [Hj | []].
    symmetry.
    exact Hj.
  - intros jobs m sched t j Hj _.
    unfold J_single in Hj.
    subst j.
    simpl.
    left.
    reflexivity.
  - intros jobs m s1 s2 t _.
    reflexivity.
Qed.

Lemma single_service_positive :
    forall t,
      1 <= t ->
      1 <= service_job 1 single_sched 0 t.
Proof.
  induction t as [| t' IH].
  - lia.
  - intros Hle.
    destruct t' as [| t''].
    + simpl.
      unfold runs_on, single_sched.
      simpl.
      lia.
    + rewrite service_job_step.
      assert (1 <= service_job 1 single_sched 0 (S t'')) by (apply IH; lia).
      lia.
Qed.

Lemma single_job_completed_after_start :
    forall t,
      1 <= t ->
      completed single_jobs 1 single_sched 0 t.
Proof.
  intros t Hle.
  unfold completed, single_jobs, single_job.
  simpl.
  pose proof (single_service_positive t Hle) as Hservice.
  lia.
Qed.

Lemma single_job_not_eligible_after_start :
    forall t,
      1 <= t ->
      ~ eligible single_jobs 1 single_sched 0 t.
Proof.
  intros t Hle [Hrel Hncomp].
  apply Hncomp.
  exact (single_job_completed_after_start t Hle).
Qed.

Lemma single_feasible_on :
    feasible_schedule_on J_single single_jobs 1 single_sched.
Proof.
  unfold feasible_schedule_on, J_single, missed_deadline.
  intros j Hj.
  subst j.
  intro Hmiss.
  apply Hmiss.
  unfold completed, single_jobs, single_job.
  simpl.
  lia.
Qed.

Lemma single_nonzero_cpu_idle :
    forall t c,
      0 < c ->
      single_sched t c = None.
Proof.
  intros t c Hc.
  unfold single_sched.
  assert (Hneq : c <> 0) by lia.
  apply Nat.eqb_neq in Hneq.
  rewrite Hneq.
  reflexivity.
Qed.

Lemma single_edf_rel :
    scheduler_rel (edf_scheduler singleton_candidates) single_jobs 1 single_sched.
Proof.
  unfold edf_scheduler, single_cpu_dispatch_schedule.
  split.
  - reflexivity.
  - intro t.
    split.
    + destruct t as [| t'].
      * unfold single_sched, singleton_candidates, choose_edf, min_dl_job,
               eligibleb, single_jobs, single_job.
        simpl.
        reflexivity.
      * unfold single_sched.
        simpl.
        symmetry.
        apply choose_edf_none_if_no_eligible.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply single_job_not_eligible_after_start.
        lia.
    + exact (single_nonzero_cpu_idle t).
Qed.

Lemma single_fifo_rel :
    scheduler_rel (fifo_scheduler singleton_candidates) single_jobs 1 single_sched.
Proof.
  unfold fifo_scheduler, single_cpu_dispatch_schedule.
  split.
  - reflexivity.
  - intro t.
    split.
    + destruct t as [| t'].
      * unfold single_sched, singleton_candidates, choose_fifo,
               eligibleb, single_jobs, single_job.
        simpl.
        reflexivity.
      * unfold single_sched.
        simpl.
        symmetry.
        change (choose_fifo single_jobs 1 single_sched (S t') [0] = None).
        apply choose_fifo_none_if_no_eligible.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply single_job_not_eligible_after_start.
        lia.
    + exact (single_nonzero_cpu_idle t).
Qed.

Theorem single_edf_schedulable_by_on :
    schedulable_by_on J_single (edf_scheduler singleton_candidates) single_jobs 1.
Proof.
  change (schedulable_by_on
            J_single
            (single_cpu_dispatch_scheduler_on
               J_single edf_generic_spec singleton_candidates singleton_candidates_spec)
            single_jobs 1).
  exact
    (single_cpu_dispatch_schedulable_by_on_intro
       J_single
       edf_generic_spec
       singleton_candidates
       singleton_candidates_spec
       single_jobs
       single_sched
       single_edf_rel
       single_feasible_on).
Qed.

Theorem single_fifo_schedulable_by_on :
    schedulable_by_on J_single (fifo_scheduler singleton_candidates) single_jobs 1.
Proof.
  change (schedulable_by_on
            J_single
            (single_cpu_dispatch_scheduler_on
               J_single fifo_generic_spec singleton_candidates singleton_candidates_spec)
            single_jobs 1).
  exact
    (single_cpu_dispatch_schedulable_by_on_intro
       J_single
       fifo_generic_spec
       singleton_candidates
       singleton_candidates_spec
       single_jobs
       single_sched
       single_fifo_rel
       single_feasible_on).
Qed.

(* ================================================================= *)
(** ** Partitioned example                                            *)
(* ================================================================= *)

Definition pair_job0 : Job := mkJob 0 0 0 1 2.
Definition pair_job1 : Job := mkJob 0 1 0 1 2.

Definition pair_jobs (j : JobId) : Job :=
  match j with
  | 0 => pair_job0
  | 1 => pair_job1
  | _ => pair_job0
  end.

Definition J_pair (j : JobId) : Prop := j = 0 \/ j = 1.

Definition assign_pair (j : JobId) : CPU :=
  if Nat.eqb j 0 then 0 else 1.

Lemma assign_pair_valid :
    forall j,
      assign_pair j < 2.
Proof.
  intro j.
  unfold assign_pair.
  destruct (Nat.eqb j 0); lia.
Qed.

Lemma enum_pair_complete :
    forall j,
      J_pair j -> In j [0; 1].
Proof.
  intros j [Hj | Hj]; subst j; simpl; auto.
Qed.

Lemma enum_pair_sound :
    forall j,
      In j [0; 1] -> J_pair j.
Proof.
  intros j Hin.
  destruct Hin as [<- | [<- | []]]; unfold J_pair; auto.
Qed.

(* Concrete per-CPU candidate source: for each CPU c, return jobs in [0;1]
   assigned to c.  Built from enum_local_candidates_of. *)
Definition pair_cands : CPU -> CandidateSource :=
  enum_local_candidates_of assign_pair [0; 1].

Lemma pair_cands_spec :
    forall c, c < 2 ->
      CandidateSourceSpec (local_jobset assign_pair J_pair c) (pair_cands c).
Proof.
  intros c Hlt.
  unfold pair_cands.
  exact (enum_local_candidates_spec assign_pair 2 J_pair [0; 1]
           enum_pair_complete enum_pair_sound c Hlt).
Qed.

Definition pair_sched (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb t 0 then
    if Nat.eqb cpu 0 then Some 0
    else if Nat.eqb cpu 1 then Some 1
    else None
  else None.

Lemma pair_job0_completed :
    completed pair_jobs 2 pair_sched 0 2.
Proof.
  unfold completed, pair_jobs, pair_job0, pair_sched.
  simpl.
  lia.
Qed.

Lemma pair_job1_completed :
    completed pair_jobs 2 pair_sched 1 2.
Proof.
  unfold completed, pair_jobs, pair_job1, pair_sched.
  simpl.
  lia.
Qed.

Lemma pair_partitioned_feasible_on :
    feasible_schedule_on J_pair pair_jobs 2 pair_sched.
Proof.
  unfold feasible_schedule_on, J_pair, missed_deadline.
  intros j [Hj | Hj].
  - subst j.
    intro Hmiss.
    exact (Hmiss pair_job0_completed).
  - subst j.
    intro Hmiss.
    exact (Hmiss pair_job1_completed).
Qed.

Lemma pair_job0_local_service_positive :
    forall t,
      1 <= t ->
      1 <= service_job 1 (cpu_schedule pair_sched 0) 0 t.
Proof.
  induction t as [| t' IH].
  - lia.
  - intros Hle.
    destruct t' as [| t''].
    + unfold cpu_schedule, runs_on, pair_sched.
      simpl.
      lia.
    + rewrite service_job_step.
      assert (1 <= service_job 1 (cpu_schedule pair_sched 0) 0 (S t'')).
      { apply IH. lia. }
      lia.
Qed.

Lemma pair_job1_local_service_positive :
    forall t,
      1 <= t ->
      1 <= service_job 1 (cpu_schedule pair_sched 1) 1 t.
Proof.
  induction t as [| t' IH].
  - lia.
  - intros Hle.
    destruct t' as [| t''].
    + unfold cpu_schedule, runs_on, pair_sched.
      simpl.
      lia.
    + rewrite service_job_step.
      assert (1 <= service_job 1 (cpu_schedule pair_sched 1) 1 (S t'')).
      { apply IH. lia. }
      lia.
Qed.

Lemma pair_job0_local_not_eligible_after_start :
    forall t,
      1 <= t ->
      ~ eligible pair_jobs 1 (cpu_schedule pair_sched 0) 0 t.
Proof.
  intros t Hle [Hrel Hncomp].
  apply Hncomp.
  unfold completed, pair_jobs, pair_job0.
  simpl.
  pose proof (pair_job0_local_service_positive t Hle) as Hservice.
  lia.
Qed.

Lemma pair_job1_local_not_eligible_after_start :
    forall t,
      1 <= t ->
      ~ eligible pair_jobs 1 (cpu_schedule pair_sched 1) 1 t.
Proof.
  intros t Hle [Hrel Hncomp].
  apply Hncomp.
  unfold completed, pair_jobs, pair_job1.
  simpl.
  pose proof (pair_job1_local_service_positive t Hle) as Hservice.
  lia.
Qed.

Lemma pair_partitioned_schedule :
    valid_partitioned_schedule 2 fifo_generic_spec pair_cands pair_jobs pair_sched.
Proof.
  apply valid_partitioned_schedule_intro.
  unfold raw_partitioned_schedule_on.
  intros t c Hlt.
  assert (Hc : c = 0 \/ c = 1) by lia.
  destruct Hc as [-> | ->].
  - destruct t as [| t'].
    + unfold pair_sched, assign_pair, cpu_schedule,
             pair_cands, enum_local_candidates_of, local_candidates.
      simpl.
      reflexivity.
    + unfold pair_sched, pair_cands, enum_local_candidates_of, local_candidates.
      simpl.
      replace
        (filter (fun j : JobId => Nat.eqb (assign_pair j) 0) [0; 1])
        with [0] by reflexivity.
      symmetry.
      change (choose_fifo pair_jobs 1 (cpu_schedule pair_sched 0) (S t') [0] = None).
      apply choose_fifo_none_if_no_eligible.
      intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj | []].
      subst j.
      apply pair_job0_local_not_eligible_after_start.
      lia.
  - destruct t as [| t'].
    + unfold pair_sched, assign_pair, cpu_schedule,
             pair_cands, enum_local_candidates_of, local_candidates.
      simpl.
      reflexivity.
    + unfold pair_sched, pair_cands, enum_local_candidates_of, local_candidates.
      simpl.
      replace
        (filter (fun j : JobId => Nat.eqb (assign_pair j) 1) [0; 1])
        with [1] by reflexivity.
      symmetry.
      change (choose_fifo pair_jobs 1 (cpu_schedule pair_sched 1) (S t') [1] = None).
      apply choose_fifo_none_if_no_eligible.
      intros j Hin.
      simpl in Hin.
      destruct Hin as [Hj | []].
      subst j.
      apply pair_job1_local_not_eligible_after_start.
      lia.
Qed.

Lemma pair_partitioned_rel :
    scheduler_rel
      (partitioned_scheduler 2 fifo_generic_spec pair_cands)
      pair_jobs 2 pair_sched.
Proof.
  unfold partitioned_scheduler, scheduler_rel.
  split.
  - reflexivity.
  - exact pair_partitioned_schedule.
Qed.

Lemma pair_partitioned_valid :
    valid_schedule pair_jobs 2 pair_sched.
Proof.
  exact (partitioned_schedule_implies_valid_schedule
           assign_pair 2 assign_pair_valid fifo_generic_spec J_pair pair_cands
           pair_cands_spec pair_jobs pair_sched pair_partitioned_schedule).
Qed.

Theorem pair_partitioned_schedulable_by_on :
    schedulable_by_on
      J_pair
      (partitioned_scheduler 2 fifo_generic_spec pair_cands)
      pair_jobs 2.
Proof.
  apply (partitioned_schedulable_by_on_intro
           2 fifo_generic_spec pair_cands J_pair pair_jobs pair_sched).
  - exact pair_partitioned_rel.
  - exact pair_partitioned_valid.
  - exact pair_partitioned_feasible_on.
Qed.

(* ================================================================= *)
(** ** Bundle-based example: edf_bundle → uni_scheduler_on           *)
(* ================================================================= *)

(* Demonstrate the UniSchedulerBundle API:
   1. Construct edf_bundle with a candidate source.
   2. Extract the concrete scheduler via uni_scheduler_on.
   3. Derive schedulable_by_on via uni_scheduler_on_schedulable_by_on_intro.

   This is the new standard entry point: callers only need to supply a
   candidate source and a feasibility witness, with no knowledge of the
   underlying dispatch machinery.                                      *)

Definition edf_single_bundle : UniSchedulerBundle J_single EDFSchedulerSpec :=
  edf_bundle J_single singleton_candidates singleton_candidates_spec.

(* The concrete EDF scheduler extracted from the bundle. *)
Definition edf_single_scheduler : Scheduler :=
  uni_scheduler_on edf_single_bundle.

(* edf_single_scheduler satisfies the scheduler relation for single_sched. *)
Lemma edf_single_bundle_rel :
    scheduler_rel edf_single_scheduler single_jobs 1 single_sched.
Proof.
  unfold edf_single_scheduler, uni_scheduler_on, edf_single_bundle, edf_bundle,
         single_cpu_dispatch_scheduler_on, single_cpu_dispatch_schedule.
  split.
  - reflexivity.
  - intro t.
    split.
    + destruct t as [| t'].
      * unfold single_sched, singleton_candidates, choose_edf, min_dl_job,
               eligibleb, single_jobs, single_job.
        simpl.
        reflexivity.
      * unfold single_sched.
        simpl.
        symmetry.
        apply choose_edf_none_if_no_eligible.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply single_job_not_eligible_after_start.
        lia.
    + exact (single_nonzero_cpu_idle t).
Qed.

(* Main result: the bundle-based EDF scheduler is schedulable for J_single. *)
Theorem edf_bundle_schedulable_by_on :
    schedulable_by_on J_single edf_single_scheduler single_jobs 1.
Proof.
  exact (uni_scheduler_on_schedulable_by_on_intro
           J_single EDFSchedulerSpec edf_single_bundle single_jobs single_sched
           edf_single_bundle_rel
           single_feasible_on).
Qed.

(* ================================================================= *)
(** ** Partitioned EDF example via PartitionedCompose                 *)
(* ================================================================= *)

(* Demonstrate local_edf_witnesses_imply_partitioned_edf_schedulable_by_on:
   reuse the pair_* infrastructure (2 jobs, 2 CPUs, static assignment)
   from the partitioned FIFO example above, but drive it with EDF.

   Per-CPU local witnesses:
     locals 0 = cpu_schedule pair_sched 0   (job 0 runs on CPU 0 at t=0)
     locals 1 = cpu_schedule pair_sched 1   (job 1 runs on CPU 1 at t=0)

   We prove each satisfies the edf_scheduler relation, then apply the
   composition theorem to obtain schedulable_by_on for the partitioned
   EDF scheduler.                                                       *)

Definition pair_locals (c : CPU) : Schedule := cpu_schedule pair_sched c.

Lemma pair_local0_edf_rel :
    scheduler_rel
      (edf_scheduler (pair_cands 0))
      pair_jobs 1 (pair_locals 0).
Proof.
  unfold edf_scheduler, single_cpu_dispatch_schedule, pair_locals.
  split.
  - reflexivity.
  - intro t.
    split.
    + destruct t as [| t'].
      * unfold pair_cands, enum_local_candidates_of, local_candidates,
               cpu_schedule, pair_sched, assign_pair, choose_edf,
               eligibleb, pair_jobs, pair_job0.
        simpl. reflexivity.
      * simpl.
        symmetry.
        change (choose_edf pair_jobs 1 (cpu_schedule pair_sched 0) (S t') [0] = None).
        apply choose_edf_none_if_no_eligible.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply pair_job0_local_not_eligible_after_start.
        lia.
    + intros c' Hc'.
      unfold cpu_schedule, pair_sched.
      destruct (Nat.eqb c' 0) eqn:E.
      * apply Nat.eqb_eq in E. lia.
      * reflexivity.
Qed.

Lemma pair_local1_edf_rel :
    scheduler_rel
      (edf_scheduler (pair_cands 1))
      pair_jobs 1 (pair_locals 1).
Proof.
  unfold edf_scheduler, single_cpu_dispatch_schedule, pair_locals.
  split.
  - reflexivity.
  - intro t.
    split.
    + destruct t as [| t'].
      * unfold pair_cands, enum_local_candidates_of, local_candidates,
               cpu_schedule, pair_sched, assign_pair, choose_edf,
               eligibleb, pair_jobs, pair_job1.
        simpl. reflexivity.
      * simpl.
        symmetry.
        change (choose_edf pair_jobs 1 (cpu_schedule pair_sched 1) (S t') [1] = None).
        apply choose_edf_none_if_no_eligible.
        intros j Hin.
        simpl in Hin.
        destruct Hin as [Hj | []].
        subst j.
        apply pair_job1_local_not_eligible_after_start.
        lia.
    + intros c' Hc'.
      unfold cpu_schedule, pair_sched.
      destruct (Nat.eqb c' 0) eqn:E.
      * apply Nat.eqb_eq in E. lia.
      * reflexivity.
Qed.

Lemma pair_local0_edf_feasible_on :
    feasible_schedule_on (local_jobset assign_pair J_pair 0) pair_jobs 1
      (pair_locals 0).
Proof.
  unfold feasible_schedule_on, local_jobset, missed_deadline, pair_locals.
  intros j [HJ Hassign].
  unfold J_pair in HJ.
  destruct HJ as [-> | ->].
  - intro Hmiss.
    apply Hmiss.
    unfold completed, pair_jobs, pair_job0.
    simpl.
    pose proof (pair_job0_local_service_positive 2 (le_S 1 1 (Nat.le_refl 1))).
    lia.
  - unfold assign_pair in Hassign. simpl in Hassign. discriminate.
Qed.

Lemma pair_local1_edf_feasible_on :
    feasible_schedule_on (local_jobset assign_pair J_pair 1) pair_jobs 1
      (pair_locals 1).
Proof.
  unfold feasible_schedule_on, local_jobset, missed_deadline, pair_locals.
  intros j [HJ Hassign].
  unfold J_pair in HJ.
  destruct HJ as [-> | ->].
  - unfold assign_pair in Hassign. simpl in Hassign. discriminate.
  - intro Hmiss.
    apply Hmiss.
    unfold completed, pair_jobs, pair_job1.
    simpl.
    pose proof (pair_job1_local_service_positive 2 (le_S 1 1 (Nat.le_refl 1))).
    lia.
Qed.

Theorem pair_partitioned_edf_schedulable_by_on :
    schedulable_by_on
      J_pair
      (partitioned_edf_scheduler 2 pair_cands)
      pair_jobs 2.
Proof.
  apply (local_edf_witnesses_imply_partitioned_edf_schedulable_by_on
           assign_pair 2 assign_pair_valid J_pair pair_cands pair_cands_spec
           pair_jobs pair_locals).
  intros c Hlt.
  assert (Hc : c = 0 \/ c = 1) by lia.
  destruct Hc as [-> | ->].
  - split.
    + exact pair_local0_edf_rel.
    + exact pair_local0_edf_feasible_on.
  - split.
    + exact pair_local1_edf_rel.
    + exact pair_local1_edf_feasible_on.
Qed.
