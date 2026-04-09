From Stdlib Require Import Arith Arith.PeanoNat Lia List.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import UniPolicies.EDF.
Require Import UniPolicies.FIFO.
Require Import Partitioned.
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
    valid_partitioned_schedule assign_pair 2 fifo_generic_spec [0; 1] pair_jobs pair_sched.
Proof.
  apply valid_partitioned_schedule_intro.
  unfold partitioned_schedule_on.
  intros t c Hlt.
  assert (Hc : c = 0 \/ c = 1) by lia.
  destruct Hc as [-> | ->].
  - destruct t as [| t'].
    + unfold pair_sched, assign_pair, cpu_schedule.
      simpl.
      reflexivity.
    + unfold pair_sched.
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
    + unfold pair_sched, assign_pair, cpu_schedule.
      simpl.
      reflexivity.
    + unfold pair_sched.
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
      (partitioned_scheduler assign_pair 2 fifo_generic_spec [0; 1])
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
           assign_pair 2 assign_pair_valid fifo_generic_spec [0; 1]
           pair_jobs pair_sched pair_partitioned_schedule).
Qed.

Theorem pair_partitioned_schedulable_by_on :
    schedulable_by_on
      J_pair
      (partitioned_scheduler assign_pair 2 fifo_generic_spec [0; 1])
      pair_jobs 2.
Proof.
  apply (partitioned_schedulable_by_on_intro
           assign_pair 2 fifo_generic_spec J_pair [0; 1] pair_jobs pair_sched).
  - exact pair_partitioned_rel.
  - exact pair_partitioned_valid.
  - exact pair_partitioned_feasible_on.
Qed.
