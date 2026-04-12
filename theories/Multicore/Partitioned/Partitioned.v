From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From SchedulingTheory Require Import Multicore.Common.MultiCoreBase.
From SchedulingTheory Require Import Abstractions.Scheduler.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.Interface.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
Import ListNotations.

(* ===== Partitioned Scheduling: Definitions and Core Theorems (Lv.5) =====

   A partitioned multiprocessor schedule statically assigns each job to exactly
   one CPU.  Each CPU runs an independent single-CPU scheduler (GenericSchedulingAlgorithm).
   The multicore schedule is the pointwise union of the per-CPU schedules.

   Core theorems proved here:
     1. partitioned_schedule_implies_respects_assignment
                             — raw_partitioned_schedule_on implies assignment respected
     2. assignment_respect   — a running job always runs on its assigned CPU
     3. partitioned_schedule_implies_valid_schedule
                             — valid_partitioned_schedule implies global validity
     4. service_decomposition — job service = service on assigned CPU only

   Bridge-style refactor (plan/todo.md):
     - PartitionedSection takes an abstract CandidateSource per CPU
       (Variable local_candidates_of) instead of a concrete enumJ list.
     - raw_partitioned_schedule_on (internal) / valid_partitioned_schedule (public
       API) distinction is stable: clients use valid_partitioned_schedule.
     - The enumJ/filter concrete implementation lives in PartitionedEnumCandidates.
     - partitioned_schedule_on_iff_local_rel aligns multicore choose with
       single_cpu_algorithm_schedule per CPU (bridge-style).
     - partitioned_schedulable_by_on_from_local is the canonical 3-step entry
       point for global schedulability from per-CPU local feasibility.

   Policy compatibility (Phase 6 confirmation):
     - EDF: use edf_generic_spec + enum_local_candidates_of (static list)
     - FIFO: use fifo_generic_spec + enum_local_candidates_of (static list)
       → see SchedulableExamples.pair_partitioned_schedulable_by_on
     - RR / prefix-dependent policies: supply a CandidateSource whose
       candidate list depends on the local schedule prefix (jobs m s t).
       The CandidateSourceSpec.candidates_prefix_extensional field ensures
       that round-robin state visible before time t is well-defined, enabling
       schedule-inductive construction. *)

(* ===== Abstract Partitioned Section ===== *)

Section PartitionedSection.

  (* Static CPU assignment: each job is permanently assigned to one CPU. *)
  Variable assign : JobId -> CPU.

  (* Number of CPUs in the partitioned system. *)
  Variable m : nat.

  (* All assigned CPUs are valid indices. *)
  Variable valid_assignment : forall j, assign j < m.

  (* Per-CPU choose policy (generic; any scheduler satisfying
     GenericSchedulingAlgorithm can be used, e.g. EDF, FIFO, RR). *)
  Variable spec : GenericSchedulingAlgorithm.

  (* The set of jobs in the system. *)
  Variable J : JobId -> Prop.

  (* local_jobset c: the set of jobs in J that are assigned to CPU c.
     Defined here so that local_candidates_spec_hyp can reference it. *)
  Definition local_jobset (c : CPU) : JobId -> Prop :=
    fun j => J j /\ assign j = c.

  (* Abstract per-CPU candidate source: replaces the concrete enumJ/filter
     approach.  Any function from CPU to CandidateSource may be provided,
     as long as it satisfies local_candidates_spec_hyp below.
     The concrete enumJ/filter instance is in PartitionedEnumCandidates. *)
  Variable local_candidates_of : CPU -> CandidateSource.

  Hypothesis local_candidates_spec_hyp :
    forall c, c < m ->
      CandidateSourceSpec (local_jobset c) (local_candidates_of c).

  (* ===== Definitions ===== *)

  (* assigned_to j c: job j is statically assigned to CPU c. *)
  Definition assigned_to (j : JobId) (c : CPU) : Prop :=
    assign j = c.

  (* respects_assignment sched: every job runs only on its assigned CPU. *)
  Definition respects_assignment (sched : Schedule) : Prop :=
    forall j t c, c < m -> sched t c = Some j -> assign j = c.

  (* partitioned_schedule_on jobs sched: the schedule is consistent with
     running the per-CPU policy on each CPU's local 1-CPU view.
     At each time step, what CPU c runs is exactly what spec would choose
     from the candidate source for c, evaluated on the local CPU view. *)
  Definition raw_partitioned_schedule_on (jobs : JobId -> Job) (sched : Schedule) : Prop :=
    forall t c, c < m ->
      sched t c =
        spec.(choose) jobs 1 (cpu_schedule sched c) t
          (local_candidates_of c jobs 1 (cpu_schedule sched c) t).

  (* valid_partitioned_schedule is the public specification predicate for
   partitioned schedulers.

   This predicate bundles two conditions:
   1. [raw_partitioned_schedule_on]: the internal choose equation — at every
      time step each CPU runs exactly what its per-CPU policy selects.
   2. [respects_assignment]: every running job executes on its statically
      assigned CPU.

   Design intent:
   - Clients should use this predicate (not [raw_partitioned_schedule_on])
     as the entry point for any partitioned-scheduler reasoning.
   - The projection lemmas [valid_partitioned_schedule_raw] and
     [valid_partitioned_schedule_respects_assignment] extract the individual
     components, keeping client proofs independent of the conjunction layout.
   - A third component ([valid_schedule]) may be added in the future; the
     projection-lemma API will absorb such changes without client churn. *)
  Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
    raw_partitioned_schedule_on jobs sched /\
    respects_assignment sched.

  (* Introduction rule for [valid_partitioned_schedule]:
     requires both the raw choose equation and assignment respect. *)
  Lemma valid_partitioned_schedule_intro :
    forall jobs sched,
      raw_partitioned_schedule_on jobs sched ->
      respects_assignment sched ->
      valid_partitioned_schedule jobs sched.
  Proof.
    intros jobs sched H1 H2. exact (conj H1 H2).
  Qed.

  (* Projection: extract [raw_partitioned_schedule_on] from [valid_partitioned_schedule]. *)
  Lemma valid_partitioned_schedule_raw :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      raw_partitioned_schedule_on jobs sched.
  Proof.
    intros jobs sched [H _]. exact H.
  Qed.

  (* Projection: extract [respects_assignment] from [valid_partitioned_schedule]. *)
  Lemma valid_partitioned_schedule_respects_assignment :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      respects_assignment sched.
  Proof.
    intros jobs sched [_ H]. exact H.
  Qed.

  (* ===== Helper Lemmas ===== *)

  (* Key new theorem: partitioned_schedule_on implies respects_assignment.
     Proof: if sched t c = Some j, then by partitioned_schedule_on the choose
     chose j from local_candidates_of c ..., so j is in that list, hence
     candidates_sound gives J j /\ assign j = c. *)
  Theorem partitioned_schedule_implies_respects_assignment :
    forall jobs sched,
      raw_partitioned_schedule_on jobs sched ->
      respects_assignment sched.
  Proof.
    intros jobs sched Hpart j t c Hlt Hrun.
    pose proof (Hpart t c Hlt) as Heq.
    rewrite Hrun in Heq.
    symmetry in Heq.
    pose proof (spec.(choose_in_candidates) jobs 1 (cpu_schedule sched c) t
                  (local_candidates_of c jobs 1 (cpu_schedule sched c) t) j Heq) as Hin.
    pose proof (local_candidates_spec_hyp c Hlt) as Hcspec.
    destruct Hcspec as [Hsound _ _].
    exact (proj2 (Hsound jobs 1 (cpu_schedule sched c) t j Hin)).
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

  (* Preferred multicore name: respects_assignment implies no_duplication. *)
  Lemma partitioned_implies_no_duplication :
    forall sched,
      respects_assignment sched ->
      no_duplication m sched.
  Proof.
    intros sched Hresp.
    apply no_duplication_iff_sequential_jobs.
    exact (partitioned_implies_sequential sched Hresp).
  Qed.

  (* H4: under respects_assignment, cpu_count collapses to 0 or 1 at assign j. *)
  Lemma cpu_count_assigned_only :
    forall sched,
      respects_assignment sched ->
      forall j t,
        cpu_count m sched j t = if runs_on sched j t (assign j) then 1 else 0.
  Proof.
    intros sched Hresp j t.
    destruct (runs_on sched j t (assign j)) eqn:Erun.
    - assert (Hpos : 0 < cpu_count m sched j t).
      { apply cpu_count_pos_iff_executed.
        exists (assign j). split.
        - exact (valid_assignment j).
        - apply runs_on_true_iff. exact Erun. }
      assert (Hle : cpu_count m sched j t <= 1).
      { apply cpu_count_le_1.
        apply partitioned_implies_sequential. exact Hresp. }
      lia.
    - apply cpu_count_zero_iff_not_executed.
      intros c Hlt Hsome.
      pose proof (Hresp j t c Hlt Hsome) as Hassign.
      apply runs_on_false_iff in Erun.
      rewrite Hassign in Erun.
      exact (Erun Hsome).
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
    simpl.
    rewrite runs_on_cpu_schedule.
    lia.
  Qed.

  (* ===== Core Theorems ===== *)

  (* partitioned_schedule_on is equivalent to each CPU satisfying the
     single-CPU choose bridge relation on its local view.
     This is the bridge alignment: partitioned multicore reduces to
     single_cpu_algorithm_schedule per CPU. *)
  Lemma partitioned_schedule_on_iff_local_rel :
    forall jobs sched,
      raw_partitioned_schedule_on jobs sched <->
      (forall c, c < m ->
        scheduler_rel
          (single_cpu_algorithm_schedule spec (local_candidates_of c))
          jobs 1 (cpu_schedule sched c)).
  Proof.
    intros jobs sched.
    unfold raw_partitioned_schedule_on, scheduler_rel, cpu_schedule.
    split.
    - intros Hpart c Hlt.
      split.
      + reflexivity.
      + intro t.
        split.
        * simpl.
          apply Hpart. exact Hlt.
        * intros c' Hc'.
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

  (* Theorem: any running job runs on its assigned CPU. *)
  Theorem assignment_respect :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      forall j t c,
        c < m -> sched t c = Some j -> assign j = c.
  Proof.
    intros jobs sched Hvps j t c Hlt Hrun.
    exact (valid_partitioned_schedule_respects_assignment jobs sched Hvps j t c Hlt Hrun).
  Qed.

  (* Theorem: partitioned_schedule_on implies global validity. *)
  Theorem partitioned_schedule_implies_valid_schedule :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      valid_schedule jobs m sched.
  Proof.
    intros jobs sched Hpart j t c Hlt Hrun.
    pose proof (valid_partitioned_schedule_raw jobs sched Hpart) as Hraw.
    pose proof (valid_partitioned_schedule_respects_assignment jobs sched Hpart) as Hresp.
    pose proof (Hraw t c Hlt) as Heq.
    rewrite Hrun in Heq. symmetry in Heq.
    pose proof (spec.(choose_eligible) jobs 1 (cpu_schedule sched c) t
                  (local_candidates_of c jobs 1 (cpu_schedule sched c) t) j Heq) as Heloc.
    unfold eligible in *.
    destruct Heloc as [Hrel Hncomp_local].
    split.
    - exact Hrel.
    - rewrite completed_iff_on_assigned_cpu by exact Hresp.
      pose proof (Hresp j t c Hlt Hrun) as Hassign.
      rewrite Hassign. exact Hncomp_local.
  Qed.

  (* ===== Deadline / Feasibility Lifting ===== *)

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
     NOTE: Use local_feasible_on_implies_global_feasible_on instead. *)
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
     feasible for all jobs in J. *)
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
      raw_partitioned_schedule_on jobs sched ->
      (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
  Proof.
    intros jobs sched Hpart Hlocal.
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched Hpart) as Hresp.
    pose proof (valid_partitioned_schedule_intro jobs sched Hpart Hresp) as Hvps.
    split.
    - apply partitioned_schedule_implies_valid_schedule. exact Hvps.
    - apply local_feasible_implies_global_feasible_schedule.
      + exact Hresp.
      + exact Hlocal.
  Qed.

  (* Combined (preferred): partitioned_schedule_on + per-CPU feasibility on
     local_jobset lifts to global validity + feasibility on J. *)
  Corollary local_valid_feasible_on_implies_global :
    forall jobs sched,
      valid_partitioned_schedule jobs sched ->
      (forall c, c < m ->
        feasible_schedule_on (local_jobset c) jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule_on J jobs m sched.
  Proof.
    intros jobs sched Hpart Hlocal.
    pose proof (valid_partitioned_schedule_respects_assignment jobs sched Hpart) as Hresp.
    split.
    - apply partitioned_schedule_implies_valid_schedule. exact Hpart.
    - apply local_feasible_on_implies_global_feasible_on.
      + exact Hresp.
      + exact Hlocal.
  Qed.

End PartitionedSection.

(* ===== Concrete Candidate Source: enumJ / filter ===== *)

(* This section provides the classic static-list implementation of
   local_candidates_of: for each CPU c, return the sublist of enumJ whose
   jobs are assigned to c.  This satisfies CandidateSourceSpec and can be
   used as the local_candidates_of argument in PartitionedSection. *)

Section PartitionedEnumCandidates.

  Variable assign : JobId -> CPU.
  Variable m : nat.
  Variable J : JobId -> Prop.
  Variable enumJ : list JobId.
  Hypothesis enumJ_complete : forall j, J j -> In j enumJ.
  Hypothesis enumJ_sound : forall j, In j enumJ -> J j.

  (* local_candidates c: sublist of enumJ assigned to CPU c. *)
  Definition local_candidates (c : CPU) : list JobId :=
    filter (fun j => Nat.eqb (assign j) c) enumJ.

  (* enum_local_candidates_of c: constant CandidateSource returning
     local_candidates c, independent of jobs / schedule / time. *)
  Definition enum_local_candidates_of (c : CPU) : CandidateSource :=
    fun _ _ _ _ => local_candidates c.

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

  (* enum_local_candidates_of satisfies CandidateSourceSpec for local_jobset. *)
  Lemma enum_local_candidates_spec :
    forall c, c < m ->
      CandidateSourceSpec (local_jobset assign J c) (enum_local_candidates_of c).
  Proof.
    intros c _Hlt.
    refine (mkCandidateSourceSpec (local_jobset assign J c) (enum_local_candidates_of c) _ _ _).
    - intros jobs m' sched t j Hin.
      unfold local_jobset, enum_local_candidates_of in *.
      simpl in Hin.
      split.
      + apply enumJ_sound.
        unfold local_candidates in Hin.
        apply filter_In in Hin.
        exact (proj1 Hin).
      + apply local_candidates_sound. exact Hin.
    - intros jobs m' sched t j [HJ Hassign] _Helig.
      unfold enum_local_candidates_of. simpl.
      apply local_candidates_complete; assumption.
    - intros jobs m' s1 s2 t _Hpre.
      unfold enum_local_candidates_of. reflexivity.
  Qed.

End PartitionedEnumCandidates.

(* ===== PartitionedAlgorithmContext ===== *)

(* A record bundling all invariants needed for a well-formed partitioned
   multiprocessor scheduler context.  Clients can build one of these to
   obtain a partitioned_scheduler together with the proofs needed to
   apply the core theorems (assignment_respect, local_valid_feasible_on,
   partitioned_schedulable_by_on_from_local, etc.).

   Fields:
     part_assign       — static CPU assignment
     part_m            — number of CPUs
     part_valid_assign — validity: every assigned CPU index is in range
     part_spec         — per-CPU choose policy
     part_J            — the job set in the system
     part_candidates   — abstract per-CPU CandidateSource
     part_cand_spec    — CandidateSourceSpec proof for every CPU *)
Record PartitionedAlgorithmContext := mkPartitionedAlgorithmContext {
  part_assign       : JobId -> CPU;
  part_m            : nat;
  part_valid_assign : forall j, part_assign j < part_m;
  part_spec         : GenericSchedulingAlgorithm;
  part_J            : JobId -> Prop;
  part_candidates   : CPU -> CandidateSource;
  part_cand_spec    :
    forall c, c < part_m ->
      CandidateSourceSpec
        (local_jobset part_assign part_J c)
        (part_candidates c)
}.

(* Build a Scheduler from a PartitionedAlgorithmContext.
   Defined after partitioned_scheduler below. *)


(* Lift the partitioned_schedule_on relation into the Scheduler abstraction.
   partitioned_scheduler holds for a global schedule whenever that schedule
   satisfies the abstract choose policy given by cands (a per-CPU
   CandidateSource).

   Note: assign is no longer an argument of partitioned_scheduler because
   the candidate source already encodes the per-CPU assignment.  Clients
   that use the enumJ/filter concrete instance can build cands via
   enum_local_candidates_of. *)
Definition partitioned_scheduler
    (n : nat)
    (spec : GenericSchedulingAlgorithm)
    (cands : CPU -> CandidateSource)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    m = n /\
    raw_partitioned_schedule_on n spec cands jobs sched).

(* Build a Scheduler from a PartitionedAlgorithmContext. *)
Definition partitioned_scheduler_of (ctx : PartitionedAlgorithmContext) : Scheduler :=
  partitioned_scheduler ctx.(part_m) ctx.(part_spec) ctx.(part_candidates).

(* Standard entry point: given a witness schedule whose scheduler_rel holds and
   which is feasible on J, conclude schedulable_by_on J.
   Mirrors single_cpu_algorithm_schedulable_by_on_intro for the partitioned case. *)
Corollary partitioned_schedulable_by_on_intro :
    forall (n : nat) (spec : GenericSchedulingAlgorithm)
           (cands : CPU -> CandidateSource)
           (J : JobId -> Prop) (jobs : JobId -> Job)
           (sched : Schedule),
      scheduler_rel (partitioned_scheduler n spec cands) jobs n sched ->
      valid_schedule jobs n sched ->
      feasible_schedule_on J jobs n sched ->
      schedulable_by_on J (partitioned_scheduler n spec cands) jobs n.
Proof.
  intros n spec cands J jobs sched Hrel Hvalid Hfeas.
  apply (schedulable_by_on_intro J (partitioned_scheduler n spec cands)
           jobs n sched Hrel Hvalid Hfeas).
Qed.

(* ===== Standard 3-step global schedulability entry point ===== *)

(* Canonical proof pattern for partitioned multicore schedulability:
     1. Prove valid_partitioned_schedule for the global schedule.
     2. Prove per-CPU local feasibility on local_jobset c.
     3. Invoke this lemma to conclude global schedulable_by_on J.

   This combines the scheduling algorithm validity check with the feasibility lifting
   and is the preferred entry point for concrete partitioned examples and
   future scheduler proofs. *)
Lemma partitioned_schedulable_by_on_from_local :
    forall (assign : JobId -> CPU) (n : nat)
           (valid_assign : forall j, assign j < n)
           (spec : GenericSchedulingAlgorithm)
           (J : JobId -> Prop)
           (cands : CPU -> CandidateSource)
           (cands_spec : forall c, c < n ->
             CandidateSourceSpec (local_jobset assign J c) (cands c))
           (jobs : JobId -> Job)
           (sched : Schedule),
      valid_partitioned_schedule assign n spec cands jobs sched ->
      (forall c, c < n ->
        feasible_schedule_on (local_jobset assign J c) jobs 1
          (cpu_schedule sched c)) ->
      schedulable_by_on J (partitioned_scheduler n spec cands) jobs n.
Proof.
  intros assign n valid_assign spec J cands cands_spec jobs sched Hvps Hlocal.
  (* Step 1: extract components from valid_partitioned_schedule *)
  pose proof (valid_partitioned_schedule_respects_assignment
                assign n spec cands jobs sched Hvps) as Hresp.
  (* Step 2: global validity from valid_partitioned_schedule *)
  pose proof (partitioned_schedule_implies_valid_schedule
                assign n valid_assign spec cands jobs sched Hvps)
    as Hvalid.
  (* Step 3: global feasibility from per-CPU local feasibility *)
  pose proof (local_feasible_on_implies_global_feasible_on
                assign n valid_assign J jobs sched Hresp Hlocal)
    as Hfeas.
  (* Step 4: build scheduler_rel from valid_partitioned_schedule *)
  apply (schedulable_by_on_intro J (partitioned_scheduler n spec cands)
           jobs n sched).
  - unfold partitioned_scheduler, scheduler_rel. split.
    + reflexivity.
    + exact (valid_partitioned_schedule_raw assign n spec cands jobs sched Hvps).
  - exact Hvalid.
  - exact Hfeas.
Qed.

Lemma partitioned_schedulable_by_on_from_local_ctx :
    forall (ctx : PartitionedAlgorithmContext)
           (jobs : JobId -> Job)
           (sched : Schedule),
      valid_partitioned_schedule
        ctx.(part_assign) ctx.(part_m) ctx.(part_spec) ctx.(part_candidates)
        jobs sched ->
      (forall c, c < ctx.(part_m) ->
        feasible_schedule_on
          (local_jobset ctx.(part_assign) ctx.(part_J) c)
          jobs 1 (cpu_schedule sched c)) ->
      schedulable_by_on
        ctx.(part_J) (partitioned_scheduler_of ctx) jobs ctx.(part_m).
Proof.
  intros ctx jobs sched Hvps Hlocal.
  unfold partitioned_scheduler_of.
  eapply (partitioned_schedulable_by_on_from_local
            ctx.(part_assign) ctx.(part_m) ctx.(part_valid_assign)
            ctx.(part_spec) ctx.(part_J) ctx.(part_candidates)
            ctx.(part_cand_spec) jobs sched).
  - exact Hvps.
  - exact Hlocal.
Qed.
