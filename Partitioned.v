From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.
Require Import UniSchedulerInterface.
Import ListNotations.

(* ===== Partitioned Scheduling: Definitions and Core Theorems (Lv.5) =====

   A partitioned multiprocessor schedule statically assigns each job to exactly
   one CPU.  Each CPU runs an independent single-CPU scheduler (GenericDispatchSpec).
   The multicore schedule is the pointwise union of the per-CPU schedules.

   Core theorems proved here:
     1. assignment_respect      — a running job always runs on its assigned CPU
     2. local_to_global_validity — per-CPU validity lifts to global validity
     3. service_decomposition   — job service = service on assigned CPU only *)

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

  (* candidates_for c jobs sched t xs: the sublist of xs whose jobs are
     assigned to CPU c.  The per-CPU scheduler will then internally filter
     for readiness via choose_g. *)
  Definition candidates_for (c : CPU) (jobs : JobId -> Job) (sched : Schedule)
      (t : Time) (xs : list JobId) : list JobId :=
    filter (fun j => Nat.eqb (assign j) c) xs.

  (* respects_assignment sched: every job runs only on its assigned CPU. *)
  Definition respects_assignment (sched : Schedule) : Prop :=
    forall j t c, c < m -> sched t c = Some j -> assign j = c.

  (* partitioned_schedule jobs sched xs: the schedule is consistent with
     running the per-CPU policy on each CPU's candidate set.
     At each time step, what CPU c runs is exactly what spec would choose
     from the jobs assigned to c. *)
  Definition partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
      (xs : list JobId) : Prop :=
    forall t c, c < m ->
      sched t c =
        spec.(choose_g) jobs m sched t (candidates_for c jobs sched t xs).

  (* valid_partitioned_schedule: the schedule is both dispatcher-consistent
     and assignment-respecting. *)
  Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule)
      (xs : list JobId) : Prop :=
    partitioned_schedule jobs sched xs /\ respects_assignment sched.

  (* ===== Phase 1: Helper Lemmas ===== *)

  (* H1: a job in candidates_for c is assigned to c. *)
  Lemma candidates_for_assign_sound :
    forall c jobs sched t xs j,
      In j (candidates_for c jobs sched t xs) -> assign j = c.
  Proof.
    intros c jobs sched t xs j Hin.
    unfold candidates_for in Hin.
    apply filter_In in Hin.
    destruct Hin as [_ Heqb].
    apply Nat.eqb_eq in Heqb.
    exact Heqb.
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
        cpu_count sched j t m = if runs_on sched j t (assign j) then 1 else 0.
  Proof.
    intros sched Hresp j t.
    destruct (runs_on sched j t (assign j)) eqn:Erun.
    - (* runs_on assign j = true: cpu_count = 1 *)
      (* Lower bound: at least 1 because assign j is running *)
      assert (Hpos : 0 < cpu_count sched j t m).
      { apply cpu_count_pos_iff_executed.
        exists (assign j). split.
        - exact (valid_assignment j).
        - apply runs_on_true_iff. exact Erun. }
      (* Upper bound: at most 1 because sequential_jobs *)
      assert (Hle : cpu_count sched j t m <= 1).
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
        cpu_count sched j t m =
          cpu_count (cpu_schedule sched (assign j)) j t 1.
  Proof.
    intros sched Hresp j t.
    rewrite cpu_count_assigned_only by exact Hresp.
    (* cpu_count ... j t 1 = (if runs_on ... j t 0 then 1 else 0) + 0 *)
    simpl.
    rewrite runs_on_cpu_schedule.
    lia.
  Qed.

  (* ===== Phase 2: Core Theorems ===== *)

  (* Theorem 3 (proved first): service on any m CPUs = service on assigned CPU only. *)
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

  (* Theorem 1: any running job runs on its assigned CPU. *)
  Theorem assignment_respect :
    forall jobs sched xs,
      valid_partitioned_schedule jobs sched xs ->
      forall j t c,
        c < m -> sched t c = Some j -> assign j = c.
  Proof.
    intros jobs sched xs [_ Hresp] j t c Hlt Hrun.
    exact (Hresp j t c Hlt Hrun).
  Qed.

  (* Theorem 2: per-CPU validity lifts to global validity. *)
  Theorem local_to_global_validity :
    forall jobs sched xs,
      valid_partitioned_schedule jobs sched xs ->
      (forall c, c < m ->
        valid_schedule jobs 1 (cpu_schedule sched c)) ->
      valid_schedule jobs m sched.
  Proof.
    intros jobs sched xs Hvps Hlocal.
    destruct Hvps as [_ Hresp].
    unfold valid_schedule.
    intros j t c Hlt Hrun.
    (* Invoke per-CPU validity for CPU c *)
    specialize (Hlocal c Hlt).
    unfold valid_schedule in Hlocal.
    (* cpu_schedule sched c at virtual-CPU 0 = sched t c = Some j *)
    assert (Hcpu : cpu_schedule sched c t 0 = Some j).
    { unfold cpu_schedule. rewrite Nat.eqb_refl. exact Hrun. }
    specialize (Hlocal j t 0 (Nat.lt_succ_diag_r 0) Hcpu).
    (* Hlocal : eligible jobs 1 (cpu_schedule sched c) j t *)
    unfold eligible in *.
    destruct Hlocal as [Hrel Hncomp].
    split.
    - exact Hrel.
    - (* ~completed jobs m sched j t *)
      rewrite completed_iff_on_assigned_cpu by exact Hresp.
      (* assign j = c because respects_assignment *)
      pose proof (Hresp j t c Hlt Hrun) as Hassign.
      rewrite Hassign.
      exact Hncomp.
  Qed.

End PartitionedSection.
