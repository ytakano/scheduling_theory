(* AffinityExamples.v
   Concrete examples that anchor the affinity / admissibility design.

   H-1. 2-CPU affinity example
        - j0 is admissible on CPU 0 only (cpu_affinity restricting to CPU 0)
        - j1 is admissible on both CPU 0 and CPU 1
        - Verify that affinity_admissibility and job_has_admissible_cpu behave
          as expected, and that both jobs satisfy the nonemptiness condition.

   H-2. Singleton vs all-cpu comparison
        - Under all_cpus_admissible: any job is admissible on any CPU.
        - Under singleton_admissibility: each job is admissible on exactly
          one statically assigned CPU, not on others.
        - The same job that is admissible under all_cpus_admissible may not
          be admissible on a particular CPU under singleton_admissibility,
          illustrating that singleton yields strictly fewer admissible pairs.
*)

From Stdlib Require Import Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.AffinityFacts.
From RocqSched Require Import Multicore.Common.AdmissibleCandidateSource.

(* ===== H-1. 2-CPU affinity example ===== *)

Section TwoCPUAffinityExample.

  (** cpu0_only: an affinity that restricts any job to CPU 0. *)
  Definition cpu0_only : cpu_affinity := fun _ c => c = 0.

  (** cpu0_or_cpu1: an affinity that allows any job on CPU 0 or CPU 1. *)
  Definition cpu0_or_cpu1 : cpu_affinity := fun _ c => c = 0 \/ c = 1.

  (** Under cpu0_only, job 0 is admissible on CPU 0. *)
  Example j0_admissible_cpu0 :
    affinity_admissibility cpu0_only 0 0.
  Proof.
    apply affinity_admissibility_spec.
    unfold cpu0_only.
    reflexivity.
  Qed.

  (** Under cpu0_only, job 0 is NOT admissible on CPU 1. *)
  Example j0_not_admissible_cpu1 :
    ~ affinity_admissibility cpu0_only 0 1.
  Proof.
    rewrite affinity_admissibility_spec.
    unfold cpu0_only.
    discriminate.
  Qed.

  (** Under cpu0_or_cpu1, job 1 is admissible on both CPUs. *)
  Example j1_admissible_cpu0 :
    affinity_admissibility cpu0_or_cpu1 1 0.
  Proof.
    apply affinity_admissibility_spec.
    unfold cpu0_or_cpu1.
    left. reflexivity.
  Qed.

  Example j1_admissible_cpu1 :
    affinity_admissibility cpu0_or_cpu1 1 1.
  Proof.
    apply affinity_admissibility_spec.
    unfold cpu0_or_cpu1.
    right. reflexivity.
  Qed.

  (** Both affinity predicates have at least one admissible CPU for every job. *)
  Example cpu0_only_nonempty :
    forall j, job_has_admissible_cpu (affinity_admissibility cpu0_only) j.
  Proof.
    intros j.
    exists 0.
    apply affinity_admissibility_spec.
    unfold cpu0_only.
    reflexivity.
  Qed.

  Example cpu0_or_cpu1_nonempty :
    forall j, job_has_admissible_cpu (affinity_admissibility cpu0_or_cpu1) j.
  Proof.
    intros j.
    exists 0.
    apply affinity_admissibility_spec.
    unfold cpu0_or_cpu1.
    left. reflexivity.
  Qed.

End TwoCPUAffinityExample.

(* ===== H-2. Singleton vs all-cpu comparison ===== *)

Section SingletonVsAllCPUExample.

  (** Static assignment: job 0 → CPU 0, job 1 → CPU 1. *)
  Definition assign_example : JobId -> CPU := fun j => j.

  (** Under all_cpus_admissible, every job is admissible on every CPU. *)
  Example all_cpus_job1_cpu0 :
    all_cpus_admissible 1 0.
  Proof.
    apply all_cpus_admissible_spec.
  Qed.

  Example all_cpus_job0_cpu1 :
    all_cpus_admissible 0 1.
  Proof.
    apply all_cpus_admissible_spec.
  Qed.

  (** Under singleton_admissibility assign_example, job 0 is admissible on
      CPU 0 (its assigned CPU). *)
  Example singleton_job0_cpu0 :
    singleton_admissibility assign_example 0 0.
  Proof.
    apply singleton_admissibility_spec.
    unfold assign_example.
    reflexivity.
  Qed.

  (** Under singleton_admissibility assign_example, job 1 is admissible on
      CPU 1 (its assigned CPU). *)
  Example singleton_job1_cpu1 :
    singleton_admissibility assign_example 1 1.
  Proof.
    apply singleton_admissibility_spec.
    unfold assign_example.
    reflexivity.
  Qed.

  (** Under singleton_admissibility assign_example, job 1 is NOT admissible
      on CPU 0 — illustrating the stricter constraint vs all_cpus_admissible. *)
  Example singleton_job1_not_cpu0 :
    ~ singleton_admissibility assign_example 1 0.
  Proof.
    rewrite singleton_admissibility_spec.
    unfold assign_example.
    discriminate.
  Qed.

  (** Nonemptiness holds for both instances. *)
  Example all_cpus_nonempty_example :
    forall j, job_has_admissible_cpu all_cpus_admissible j.
  Proof.
    exact all_cpus_admissible_nonempty.
  Qed.

  Example singleton_nonempty_example :
    forall j, job_has_admissible_cpu (singleton_admissibility assign_example) j.
  Proof.
    exact (singleton_admissibility_nonempty assign_example).
  Qed.

  (** The equality lemma: all_cpus_admissible is a special case of
      affinity_admissibility (with the constant True predicate). *)
  Example all_cpus_is_affinity :
    forall j cpu,
      all_cpus_admissible j cpu <->
      affinity_admissibility (fun _ _ => True) j cpu.
  Proof.
    exact all_cpus_admissible_eq_affinity.
  Qed.

  (** The equality lemma: singleton_admissibility is a special case of
      affinity_admissibility. *)
  Example singleton_is_affinity :
    forall j cpu,
      singleton_admissibility assign_example j cpu <->
      affinity_admissibility (fun j' cpu' => cpu' = assign_example j') j cpu.
  Proof.
    exact (singleton_admissibility_eq_affinity assign_example).
  Qed.

End SingletonVsAllCPUExample.

(* ===== H-3. Connection to AdmissibleCandidateSourceSpec ===== *)

(** H-3.  Any CandidateSourceSpec lifts to AdmissibleCandidateSourceSpec for any adm.

    This is the bridge between the concrete admissibility predicates above and the
    theorem layer in TopMAdmissibilityBridge.v.  For a candidate source satisfying
    the standard CandidateSourceSpec, the weaker AdmissibleCandidateSourceSpec holds
    for any adm — including cpu0_only, cpu0_or_cpu1, all_cpus_admissible, etc.

    StrongAdmissibleCandidateSourceSpec requires the additional obligation that every
    candidate is admissible somewhere.  This is needed for the generic idle-if-none
    theorem (top_m_algorithm_all_cpus_idle_if_no_subset_admissible_somewhere_gen) but
    is not required for the busy or running variants. *)

Example candidate_source_spec_lifts_to_admissible :
  forall adm J candidates_of,
    CandidateSourceSpec J candidates_of ->
    AdmissibleCandidateSourceSpec adm J candidates_of.
Proof.
  intros adm J candidates_of Hcand.
  exact (candidate_source_spec_to_admissible adm J candidates_of Hcand).
Qed.
