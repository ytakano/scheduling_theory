From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Import ListNotations.

(* ===== Partitioned Scheduling: Definitions and Core Theorems (Lv.5) =====

   A partitioned multiprocessor schedule statically assigns each job to exactly
   one CPU.  Each CPU runs an independent single-CPU scheduler (GenericDispatchSpec).
   The multicore schedule is the pointwise union of the per-CPU schedules.

   Core theorems proved here:
     1. partitioned_schedule_implies_respects_assignment
                             — partitioned_schedule_on implies assignment is respected
     2. assignment_respect   — a running job always runs on its assigned CPU
     3. partitioned_schedule_implies_valid_schedule
                             — partitioned_schedule_on implies global validity
     4. service_decomposition — job service = service on assigned CPU only *)

Section PartitionedSection.

  (* Static CPU assignment: each job is permanently assigned to one CPU. *)
  Variable assign : JobId -> CPU.

  (* Number of CPUs in the partitioned system. *)
  Variable m : nat.

  (* All assigned CPUs are valid indices. *)
  Variable valid_assignment : forall j, assign j < m.

  (* Per-CPU dispatch policy (generic; any scheduler satisfying
     GenericDispatchSpec can be used, e.g. EDF, FIFO, RR). *)
  Variable spec : GenericDispatchSpec.

  (* The set of jobs in the system. *)
  Variable J : JobId -> Prop.

  (* A finite enumeration of J: every job in J appears in enumJ. *)
  Variable enumJ : list JobId.
  Hypothesis enumJ_complete : forall j, J j -> In j enumJ.
  (* Every element of enumJ belongs to J (enumJ is a faithful enumeration). *)
  Hypothesis enumJ_sound : forall j, In j enumJ -> J j.

  (* ===== Definitions ===== *)

  (* assigned_to j c: job j is statically assigned to CPU c. *)
  Definition assigned_to (j : JobId) (c : CPU) : Prop :=
    assign j = c.

  (* cpu_schedule sched c: the single-CPU view of CPU c from the global schedule.
     Maps time t and the "virtual CPU 0" to sched t c.  All other virtual CPUs
     return None (unused in the 1-CPU view). *)
  Definition cpu_schedule (sched : Schedule) (c : CPU) : Schedule :=
    fun t' cpu' => if Nat.eqb cpu' 0 then sched t' c else None.

  (* local_candidates c: the sublist of enumJ whose jobs are assigned to CPU c.
     The per-CPU scheduler dispatches from this list. *)
  Definition local_candidates (c : CPU) : list JobId :=
    filter (fun j => Nat.eqb (assign j) c) enumJ.

  (* respects_assignment sched: every job runs only on its assigned CPU. *)
  Definition respects_assignment (sched : Schedule) : Prop :=
    forall j t c, c < m -> sched t c = Some j -> assign j = c.

  (* partitioned_schedule_on jobs sched: the schedule is consistent with
     running the per-CPU policy on each CPU's local 1-CPU view.
     At each time step, what CPU c runs is exactly what spec would choose
     from the jobs assigned to c, looking only at that CPU's local schedule. *)
  Definition partitioned_schedule_on (jobs : JobId -> Job) (sched : Schedule) : Prop :=
    forall t c, c < m ->
      sched t c =
        spec.(dispatch) jobs 1 (cpu_schedule sched c) t (local_candidates c).

  (* valid_partitioned_schedule is the public specification predicate for
   partitioned schedulers.

   Current status:
   - At the moment, this is just an alias of [partitioned_schedule_on].

   Design intent:
   - We keep this name as an abstraction boundary.
   - In the future, this predicate is expected to be strengthened to include
     additional well-formedness / validity conditions of a partitioned schedule,
     such as assignment-respect and global schedule validity.

   Usage guideline:
   - Client code should preferably state results in terms of
     [valid_partitioned_schedule] rather than [partitioned_schedule_on],
     so that future strengthening of the definition causes minimal churn. *)
  Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
    partitioned_schedule_on jobs sched.

  (* Public introduction rule for [valid_partitioned_schedule].

     Keep clients using this lemma instead of unfolding the definition directly,
     since [valid_partitioned_schedule] is intended to remain the stable
     interface-level predicate even if its underlying definition is strengthened
     later. *)
  Lemma valid_partitioned_schedule_intro :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      valid_partitioned_schedule jobs sched.
  Proof.
    intros jobs sched H. exact H.
  Qed.

  (* Elimination rule for [valid_partitioned_schedule].

     This exposes the current underlying predicate.  It is mainly useful inside
     library proofs; client-facing developments should usually prefer reasoning
     via the stable [valid_partitioned_schedule] interface when possible. *)
  Lemma valid_partitioned_schedule_elim :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      partitioned_schedule_on jobs sched.
  Proof.
    intros jobs sched H. exact H.
  Qed.

  (* ===== Bridge Abstractions ===== *)

  (* local_jobset c: the set of jobs in J that are assigned to CPU c. *)
  Definition local_jobset (c : CPU) : JobId -> Prop :=
    fun j => J j /\ assign j = c.

  (* local_candidates_of c: a constant CandidateSource that always returns
     local_candidates c.  It does not depend on jobs, schedule, or time. *)
  Definition local_candidates_of (c : CPU) : CandidateSource :=
    fun _ _ _ _ => local_candidates c.

  (* ===== Phase 1: Helper Lemmas ===== *)

  (* H0: every job in local_candidates c is assigned to c. *)
  Lemma local_candidates_sound :
    forall c j,
      In j (local_candidates c) -> assign j = c.
  Proof.
    intros c j Hin.
    unfold local_candidates in Hin.
    apply filter_In in Hin.
    destruct Hin as [_ Heqb].
    apply Nat.eqb_eq in Heqb.
    exact Heqb.
  Qed.

  (* H0b: every job in J that is assigned to c appears in local_candidates c. *)
  Lemma local_candidates_complete :
    forall j c,
      J j -> assign j = c -> In j (local_candidates c).
  Proof.
    intros j c HJ Hassign.
    unfold local_candidates.
    apply filter_In.
    split.
    - apply enumJ_complete. exact HJ.
    - apply Nat.eqb_eq. exact Hassign.
  Qed.

  (* local_candidates_of satisfies CandidateSourceSpec for local_jobset c. *)
  Lemma local_candidates_spec :
    forall c, c < m ->
      CandidateSourceSpec (local_jobset c) (local_candidates_of c).
  Proof.
    intros c _Hlt.
    refine (mkCandidateSourceSpec (local_jobset c) (local_candidates_of c) _ _ _).
    - (* soundness: candidate ∈ local_candidates c → J j ∧ assign j = c *)
      intros jobs m' sched t j Hin.
      unfold local_jobset, local_candidates_of in *.
      simpl in Hin.
      split.
      + apply enumJ_sound.
        unfold local_candidates in Hin.
        apply filter_In in Hin.
        exact (proj1 Hin).
      + apply local_candidates_sound. exact Hin.
    - (* completeness: J j ∧ assign j = c ∧ eligible → j ∈ candidates *)
      intros jobs m' sched t j [HJ Hassign] _Helig.
      unfold local_candidates_of. simpl.
      apply local_candidates_complete; assumption.
    - (* prefix extensionality: constant source, independent of schedule *)
      intros jobs m' s1 s2 t _Hpre.
      unfold local_candidates_of. reflexivity.
  Qed.

  (* Key new theorem: partitioned_schedule_on implies respects_assignment.
     Proof: if sched t c = Some j, then by partitioned_schedule_on the dispatch
     chose j from local_candidates c, so j ∈ local_candidates c, hence
     assign j = c. *)
  Theorem partitioned_schedule_implies_respects_assignment :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      respects_assignment sched.
  Proof.
    intros jobs sched Hpart j t c Hlt Hrun.
    pose proof (Hpart t c Hlt) as Heq.
    rewrite Hrun in Heq.
    symmetry in Heq.
    apply (local_candidates_sound c j).
    eapply spec.(dispatch_in_candidates).
    exact Heq.
  Qed.

  (* H2: under respects_assignment, a job only appears on its assigned CPU. *)
  Lemma non_assigned_cpu_zero :
    forall sched,
      respects_assignment sched ->
      forall j t c,
        c < m -> c <> assign j -> runs_on sched j t c = false.
  Proof.
    intros sched Hresp j t c Hlt Hneq.
    apply runs_on_false_iff.
    intro Hsome.
    apply Hneq.
    symmetry. exact (Hresp j t c Hlt Hsome).
  Qed.

  (* H3: respects_assignment implies sequential_jobs. *)
  Lemma partitioned_implies_sequential :
    forall sched,
      respects_assignment sched ->
      sequential_jobs m sched.
  Proof.
    intros sched Hresp j t c1 c2 Hlt1 Hlt2 Hc1 Hc2.
    pose proof (Hresp j t c1 Hlt1 Hc1) as Ha1.
    pose proof (Hresp j t c2 Hlt2 Hc2) as Ha2.
    lia.
  Qed.

  (* H4: under respects_assignment, cpu_count collapses to 0 or 1 at assign j.
     Proof: case split on runs_on, using cpu_count_zero/pos lemmas directly. *)
  Lemma cpu_count_assigned_only :
    forall sched,
      respects_assignment sched ->
      forall j t,
        cpu_count m sched j t = if runs_on sched j t (assign j) then 1 else 0.
  Proof.
    intros sched Hresp j t.
    destruct (runs_on sched j t (assign j)) eqn:Erun.
    - (* runs_on assign j = true: cpu_count = 1 *)
      (* Lower bound: at least 1 because assign j is running *)
      assert (Hpos : 0 < cpu_count m sched j t).
      { apply cpu_count_pos_iff_executed.
        exists (assign j). split.
        - exact (valid_assignment j).
        - apply runs_on_true_iff. exact Erun. }
      (* Upper bound: at most 1 because sequential_jobs *)
      assert (Hle : cpu_count m sched j t <= 1).
      { apply cpu_count_le_1.
        apply partitioned_implies_sequential. exact Hresp. }
      lia.
    - (* runs_on assign j = false: cpu_count = 0 *)
      apply cpu_count_zero_iff_not_executed.
      intros c Hlt Hsome.
      (* any CPU c < m that runs j must equal assign j *)
      pose proof (Hresp j t c Hlt Hsome) as Hassign.
      (* but runs_on assign j = false means sched t (assign j) ≠ Some j *)
      apply runs_on_false_iff in Erun.
      (* Hassign : assign j = c, so sched t (assign j) = sched t c = Some j *)
      rewrite Hassign in Erun.
      exact (Erun Hsome).
  Qed.

  (* H5a: runs_on through cpu_schedule at virtual-CPU 0 equals the original. *)
  Lemma runs_on_cpu_schedule :
    forall sched c j t,
      runs_on (cpu_schedule sched c) j t 0 = runs_on sched j t c.
  Proof.
    intros sched c j t.
    unfold runs_on, cpu_schedule. simpl. reflexivity.
  Qed.

  (* H5: bridge — cpu_count m equals cpu_count 1 on assigned CPU. *)
  Lemma service_decomposition_step :
    forall sched,
      respects_assignment sched ->
      forall j t,
        cpu_count m sched j t =
          cpu_count 1 (cpu_schedule sched (assign j)) j t.
  Proof.
    intros sched Hresp j t.
    rewrite cpu_count_assigned_only by exact Hresp.
    (* cpu_count ... j t 1 = (if runs_on ... j t 0 then 1 else 0) + 0 *)
    simpl.
    rewrite runs_on_cpu_schedule.
    lia.
  Qed.

  (* ===== Phase 2: Core Theorems ===== *)

  (* partitioned_schedule_on is equivalent to each CPU satisfying the
     single-CPU dispatch bridge relation on its local view. *)
  Lemma partitioned_schedule_on_iff_local_rel :
    forall jobs sched,
      partitioned_schedule_on jobs sched <->
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_dispatch_schedule spec (local_candidates_of c))
          jobs 1 (cpu_schedule sched c)).
  Proof.
    intros jobs sched.
    unfold partitioned_schedule_on, scheduler_rel, local_candidates_of, cpu_schedule.
    split.
    - intros Hpart c Hlt.
      split.
      + reflexivity.
      + intro t.
        split.
        * (* virtual CPU 0 of cpu_schedule sched c at time t = sched t c *)
          simpl.
          apply Hpart. exact Hlt.
        * (* other virtual CPUs are idle *)
          intros c' Hc'.
          simpl.
          destruct (Nat.eqb c' 0) eqn:Heqb.
          -- apply Nat.eqb_eq in Heqb. lia.
          -- reflexivity.
    - intros Hlocal t c Hlt.
      destruct (Hlocal c Hlt) as [_ Hstep].
      destruct (Hstep t) as [Heq0 _].
      simpl in Heq0.
      exact Heq0.
  Qed.

  (* Theorem: service on any m CPUs = service on assigned CPU only. *)
  Theorem service_decomposition :
    forall sched,
      respects_assignment sched ->
      forall j t,
        service_job m sched j t =
          service_job 1 (cpu_schedule sched (assign j)) j t.
  Proof.
    intros sched Hresp j t.
    induction t as [| t' IH].
    - reflexivity.
    - simpl.
      rewrite IH.
      f_equal.
      apply service_decomposition_step. exact Hresp.
  Qed.

  (* Corollary: completion on m CPUs iff completion on assigned CPU only. *)
  Corollary completed_iff_on_assigned_cpu :
    forall jobs sched,
      respects_assignment sched ->
      forall j t,
        completed jobs m sched j t <->
          completed jobs 1 (cpu_schedule sched (assign j)) j t.
  Proof.
    intros jobs sched Hresp j t.
    unfold completed.
    rewrite service_decomposition by exact Hresp.
    tauto.
  Qed.

  (* Theorem: any running job runs on its assigned CPU.
     Now follows directly from partitioned_schedule_implies_respects_assignment. *)
  Theorem assignment_respect :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      forall j t c,
        c < m -> sched t c = Some j -> assign j = c.
  Proof.
    intros jobs sched Hvps j t c Hlt Hrun.
    exact (partitioned_schedule_implies_respects_assignment jobs sched Hvps j t c Hlt Hrun).
  Qed.

  (* Theorem: partitioned_schedule_on implies global validity.
     Proof: from dispatch_eligible, j is eligible in the local 1-CPU view;
     lift to global eligibility using completed_iff_on_assigned_cpu
     (with derived respects_assignment). *)
  Theorem partitioned_schedule_implies_valid_schedule :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      valid_schedule jobs m sched.
  Proof.
    intros jobs sched Hpart j t c Hlt Hrun.
    (* Derive respects_assignment *)
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched Hpart) as Hresp.
    (* From partitioned_schedule_on: dispatch chose Some j *)
    pose proof (Hpart t c Hlt) as Heq.
    rewrite Hrun in Heq. symmetry in Heq.
    (* dispatch_eligible: j is eligible in the local 1-CPU view *)
    pose proof (spec.(dispatch_eligible) jobs 1 (cpu_schedule sched c) t (local_candidates c) j Heq) as Heloc.
    unfold eligible in *.
    destruct Heloc as [Hrel Hncomp_local].
    split.
    - exact Hrel.
    - (* lift ¬completed from local to global *)
      rewrite completed_iff_on_assigned_cpu by exact Hresp.
      pose proof (Hresp j t c Hlt Hrun) as Hassign. (* assign j = c *)
      rewrite Hassign. exact Hncomp_local.
  Qed.

  (* ===== Phase 3: Deadline / Feasibility Lifting ===== *)

  (* M1: deadline miss on the global m-CPU schedule iff deadline miss on the
     1-CPU view of the assigned CPU. *)
  Corollary missed_deadline_iff_on_assigned_cpu :
    forall jobs sched j,
      respects_assignment sched ->
      missed_deadline jobs m sched j <->
        missed_deadline jobs 1 (cpu_schedule sched (assign j)) j.
  Proof.
    intros jobs sched j Hresp.
    unfold missed_deadline.
    pose proof (completed_iff_on_assigned_cpu jobs sched Hresp j
                  (job_abs_deadline (jobs j))) as Hiff.
    tauto.
  Qed.

  (* M2 (deprecated): if every per-CPU 1-CPU schedule is feasible for ALL jobs,
     the global schedule is feasible.
     NOTE: This assumption is too strong for partitioned scheduling, where each
     CPU only needs to be feasible for the jobs assigned to it.
     Use `local_feasible_on_implies_global_feasible_on` instead. *)
  Theorem local_feasible_implies_global_feasible_schedule :
    forall jobs sched,
      respects_assignment sched ->
      (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      feasible_schedule jobs m sched.
  Proof.
    intros jobs sched Hresp Hlocal.
    unfold feasible_schedule.
    intro j.
    pose proof (valid_assignment j) as Hlt.
    pose proof (Hlocal (assign j) Hlt) as Hfeas.
    unfold feasible_schedule in Hfeas.
    pose proof (Hfeas j) as Hnmiss.
    rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp.
    exact Hnmiss.
  Qed.

  (* M2 (preferred): if every per-CPU 1-CPU schedule is feasible for the
     jobs assigned to that CPU (local_jobset c), the global schedule is
     feasible for all jobs in J.
     This is the natural assumption for partitioned scheduling. *)
  Theorem local_feasible_on_implies_global_feasible_on :
    forall jobs sched,
      respects_assignment sched ->
      (forall c, c < m ->
        feasible_schedule_on (local_jobset c) jobs 1 (cpu_schedule sched c)) ->
      feasible_schedule_on J jobs m sched.
  Proof.
    intros jobs sched Hresp Hlocal.
    unfold feasible_schedule_on.
    intros j HJ.
    pose proof (valid_assignment j) as Hlt.
    pose proof (Hlocal (assign j) Hlt) as Hfeas.
    unfold feasible_schedule_on in Hfeas.
    rewrite missed_deadline_iff_on_assigned_cpu by exact Hresp.
    apply Hfeas.
    unfold local_jobset.
    split.
    - exact HJ.
    - reflexivity.
  Qed.

  (* Combined (deprecated): use local_valid_feasible_on_implies_global instead. *)
  Corollary local_valid_feasible_implies_global :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
  Proof.
    intros jobs sched Hpart Hlocal.
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched Hpart) as Hresp.
    split.
    - apply partitioned_schedule_implies_valid_schedule. exact Hpart.
    - apply local_feasible_implies_global_feasible_schedule.
      + exact Hresp.
      + exact Hlocal.
  Qed.

  (* Combined (preferred): partitioned_schedule_on + per-CPU feasibility on
     local_jobset lifts to global validity + feasibility on J. *)
  Corollary local_valid_feasible_on_implies_global :
    forall jobs sched,
      partitioned_schedule_on jobs sched ->
      (forall c, c < m ->
        feasible_schedule_on (local_jobset c) jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule_on J jobs m sched.
  Proof.
    intros jobs sched Hpart Hlocal.
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched Hpart) as Hresp.
    split.
    - apply partitioned_schedule_implies_valid_schedule. exact Hpart.
    - apply local_feasible_on_implies_global_feasible_on.
      + exact Hresp.
      + exact Hlocal.
  Qed.

End PartitionedSection.

(* Lift the partitioned_schedule_on relation into the Scheduler abstraction.
   partitioned_scheduler holds for a global schedule whenever that schedule
   satisfies the static-assignment dispatch policy enumerated by enumJ.
   Note: valid_partitioned_schedule is parameterised by (assign, n, spec, enumJ)
   only — the job-set predicate J does not appear in the dispatch relation itself
   (only in the completeness lemma local_candidates_complete). *)
Definition partitioned_scheduler
    (assign : JobId -> CPU)
    (n : nat)
    (spec : GenericDispatchSpec)
    (enumJ : list JobId)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    m = n /\
    valid_partitioned_schedule assign n spec enumJ jobs sched).

(* Standard entry point: given a witness schedule whose scheduler_rel holds and
   which is feasible on J, conclude schedulable_by_on J.
   Mirrors single_cpu_dispatch_schedulable_by_on_intro for the partitioned case. *)
Corollary partitioned_schedulable_by_on_intro :
    forall (assign : JobId -> CPU) (m : nat) (spec : GenericDispatchSpec)
           (J : JobId -> Prop) (enumJ : list JobId) (jobs : JobId -> Job)
           (sched : Schedule),
      scheduler_rel (partitioned_scheduler assign m spec enumJ) jobs m sched ->
      valid_schedule jobs m sched ->
      feasible_schedule_on J jobs m sched ->
      schedulable_by_on J (partitioned_scheduler assign m spec enumJ) jobs m.
Proof.
  intros assign m spec J enumJ jobs sched Hrel Hvalid Hfeas.
  apply (schedulable_by_on_intro J (partitioned_scheduler assign m spec enumJ)
           jobs m sched Hrel Hvalid Hfeas).
Qed.
