From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Import ListNotations.

(* ===== Partitioned Scheduling: Definitions and Core Theorems (Lv.5) =====

   A partitioned multiprocessor schedule statically assigns each job to exactly
   one CPU.  Each CPU runs an independent single-CPU scheduler (GenericDispatchSpec).
   The multicore schedule is the pointwise union of the per-CPU schedules.

   Core theorems proved here:
     1. partitioned_schedule_implies_respects_assignment
                             — partitioned_schedule implies assignment is respected
     2. assignment_respect   — a running job always runs on its assigned CPU
     3. partitioned_schedule_implies_valid_schedule
                             — partitioned_schedule implies global validity
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

  (* ===== Definitions ===== *)

  (* assigned_to j c: job j is statically assigned to CPU c. *)
  Definition assigned_to (j : JobId) (c : CPU) : Prop :=
    assign j = c.

  (* cpu_schedule sched c: the single-CPU view of CPU c from the global schedule.
     Maps time t and the "virtual CPU 0" to sched t c.  All other virtual CPUs
     return None (unused in the 1-CPU view). *)
  Definition cpu_schedule (sched : Schedule) (c : CPU) : Schedule :=
    fun t' cpu' => if Nat.eqb cpu' 0 then sched t' c else None.

  (* candidates_for c xs: the sublist of xs whose jobs are assigned to CPU c.
     The per-CPU scheduler will then internally filter for readiness via dispatch. *)
  Definition candidates_for (c : CPU) (xs : list JobId) : list JobId :=
    filter (fun j => Nat.eqb (assign j) c) xs.

  (* respects_assignment sched: every job runs only on its assigned CPU. *)
  Definition respects_assignment (sched : Schedule) : Prop :=
    forall j t c, c < m -> sched t c = Some j -> assign j = c.

  (* partitioned_schedule jobs sched xs: the schedule is consistent with
     running the per-CPU policy on each CPU's local 1-CPU view.
     At each time step, what CPU c runs is exactly what spec would choose
     from the jobs assigned to c, looking only at that CPU's local schedule. *)
  Definition partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
      (xs : list JobId) : Prop :=
    forall t c, c < m ->
      sched t c =
        spec.(dispatch) jobs 1 (cpu_schedule sched c) t (candidates_for c xs).

  (* valid_partitioned_schedule: alias for partitioned_schedule.
     respects_assignment is now a derived consequence (see
     partitioned_schedule_implies_respects_assignment below). *)
  Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
      (xs : list JobId) : Prop :=
    partitioned_schedule jobs sched xs.

  (* ===== Phase 1: Helper Lemmas ===== *)

  (* H1: a job in candidates_for c is assigned to c. *)
  Lemma candidates_for_assign_sound :
    forall c xs j,
      In j (candidates_for c xs) -> assign j = c.
  Proof.
    intros c xs j Hin.
    unfold candidates_for in Hin.
    apply filter_In in Hin.
    destruct Hin as [_ Heqb].
    apply Nat.eqb_eq in Heqb.
    exact Heqb.
  Qed.

  (* Key new theorem: partitioned_schedule implies respects_assignment.
     Proof: if sched t c = Some j, then by partitioned_schedule the dispatch
     chose j from candidates_for c xs, so j ∈ candidates_for c xs, hence
     assign j = c. *)
  Theorem partitioned_schedule_implies_respects_assignment :
    forall jobs sched xs,
      partitioned_schedule jobs sched xs ->
      respects_assignment sched.
  Proof.
    intros jobs sched xs Hpart j t c Hlt Hrun.
    pose proof (Hpart t c Hlt) as Heq.
    (* Heq : sched t c = dispatch ... (candidates_for c xs) *)
    (* Hrun : sched t c = Some j *)
    rewrite Hrun in Heq.
    (* Heq : Some j = dispatch ... *)
    symmetry in Heq.
    apply (candidates_for_assign_sound c xs j).
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
    forall jobs sched xs,
      valid_partitioned_schedule jobs sched xs ->
      forall j t c,
        c < m -> sched t c = Some j -> assign j = c.
  Proof.
    intros jobs sched xs Hvps j t c Hlt Hrun.
    exact (partitioned_schedule_implies_respects_assignment jobs sched xs Hvps j t c Hlt Hrun).
  Qed.

  (* Theorem: partitioned_schedule implies global validity.
     Proof: from dispatch_ready, j is ready in the local 1-CPU view,
     hence eligible locally; lift to global eligibility using
     completed_iff_on_assigned_cpu (with derived respects_assignment). *)
  Theorem partitioned_schedule_implies_valid_schedule :
    forall jobs sched xs,
      partitioned_schedule jobs sched xs ->
      valid_schedule jobs m sched.
  Proof.
    intros jobs sched xs Hpart j t c Hlt Hrun.
    (* Derive respects_assignment *)
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched xs Hpart) as Hresp.
    (* From partitioned_schedule: dispatch chose Some j *)
    pose proof (Hpart t c Hlt) as Heq.
    rewrite Hrun in Heq. symmetry in Heq.
    (* dispatch_ready: j is ready in the local 1-CPU view *)
    pose proof (spec.(dispatch_ready) jobs 1 (cpu_schedule sched c) t (candidates_for c xs) j Heq) as Hready.
    (* ready → eligible *)
    unfold ready in Hready. destruct Hready as [Heloc _].
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

  (* M2: if every per-CPU 1-CPU schedule is feasible, the global schedule is feasible. *)
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

  (* Combined: partitioned_schedule + per-CPU feasibility lifts to global
     validity + feasibility. *)
  Corollary local_valid_feasible_implies_global :
    forall jobs sched xs,
      partitioned_schedule jobs sched xs ->
      (forall c, c < m -> feasible_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched /\ feasible_schedule jobs m sched.
  Proof.
    intros jobs sched xs Hpart Hlocal.
    pose proof (partitioned_schedule_implies_respects_assignment jobs sched xs Hpart) as Hresp.
    split.
    - apply partitioned_schedule_implies_valid_schedule with xs. exact Hpart.
    - apply local_feasible_implies_global_feasible_schedule.
      + exact Hresp.
      + exact Hlocal.
  Qed.

End PartitionedSection.

(* Lift the partitioned_schedule relation into the Scheduler abstraction.
   partitioned_scheduler holds for a global schedule whenever that schedule
   satisfies the static-assignment dispatch policy for xs. *)
Definition partitioned_scheduler
    (assign : JobId -> CPU)
    (n : nat)
    (spec : GenericDispatchSpec)
    (xs : list JobId)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    m = n /\
    valid_partitioned_schedule assign n spec jobs sched xs).
