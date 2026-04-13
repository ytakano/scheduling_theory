(* TopMAdmissibilityBridge.v
   Policy-independent multicore busy/idle/running lemmas for
   all_cpus_admissible.

   The three "admissible_somewhere" variants of the work-conserving
   lemmas were previously duplicated verbatim in GlobalEDF.v and
   GlobalLLF.v.  This file extracts them once, parameterised by
   spec : GenericTopMSchedulingAlgorithm, following the same naming
   convention as TopMSchedulerBridge.v.

   GlobalEDF and GlobalLLF now delegate to these lemmas and provide
   thin EDF-/LLF-specific wrappers that preserve the old public names.

   Contents
   --------
   top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere
   top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere
   top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere
*)

From Stdlib Require Import List Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.

(** D-1. If every J-job lacks admissibility somewhere (under all_cpus_admissible),
    then all CPUs are idle.

    Reduces to top_m_algorithm_all_cpus_idle_if_no_subset_eligible via
    admissible_somewhere_of_all_cpus_admissible. *)
Lemma top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (forall j, J j -> ~ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    all_cpus_idle m sched t.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hm Hnone.
  apply (top_m_algorithm_all_cpus_idle_if_no_subset_eligible
           J spec candidates_of jobs m sched t Hcand Hrel).
  intros j Hj Helig.
  apply (Hnone j Hj).
  exact (admissible_somewhere_of_all_cpus_admissible jobs m sched j t Hm Helig).
Qed.

(** D-2. If some J-job is admissible somewhere (under all_cpus_admissible),
    then at least one CPU is busy.

    Reduces via eligible_on_cpu_implies_eligible. *)
Lemma top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    (exists j, J j /\ admissible_somewhere all_cpus_admissible jobs m sched j t) ->
    exists c, c < m /\ cpu_busy sched t c.
Proof.
  intros J spec candidates_of jobs m sched t Hcand Hrel Hm [j [HJ Hadm]].
  apply (top_m_algorithm_some_cpu_busy_if_subset_eligible
           J spec candidates_of jobs m sched t Hcand Hrel Hm).
  exists j. split; [exact HJ |].
  destruct Hadm as [c Helig].
  exact (eligible_on_cpu_implies_eligible all_cpus_admissible jobs m sched j t c Helig).
Qed.

(** D-3. If some CPU is idle and a J-job is admissible somewhere (under
    all_cpus_admissible), then that job is running.

    Reduces via eligible_on_cpu_implies_eligible. *)
Lemma top_m_algorithm_running_if_some_cpu_idle_and_subset_admissible_somewhere :
  forall J spec candidates_of jobs m sched t j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (top_m_algorithm_schedule spec candidates_of) jobs m sched ->
    0 < m ->
    some_cpu_idle m sched t ->
    J j ->
    admissible_somewhere all_cpus_admissible jobs m sched j t ->
    running m sched j t.
Proof.
  intros J spec candidates_of jobs m sched t j Hcand Hrel Hm Hidle HJ Hadm.
  apply (top_m_algorithm_running_if_some_cpu_idle_and_subset_eligible
           J spec candidates_of jobs m sched t j Hcand Hrel Hidle HJ).
  destruct Hadm as [c Helig].
  exact (eligible_on_cpu_implies_eligible all_cpus_admissible jobs m sched j t c Helig).
Qed.
