(* AffinityFacts.v
   Pointwise specification lemmas for affinity_admissibility,
   all_cpus_admissible, and singleton_admissibility.

   Complements Admissibility.v (which holds definitions and equational
   embedding lemmas) with per-pair unfolding facts that let callers avoid
   manual unfold chains.

   Contents
   --------
   affinity_admissibility_spec     : affinity_admissibility aff j cpu <-> aff j cpu
   all_cpus_admissible_spec        : all_cpus_admissible j cpu  (always True)
   singleton_admissibility_spec    : singleton_admissibility assign j cpu <-> cpu = assign j
   (* singleton_admissibility_unique is already in Admissibility.v and
      is inherited via that module's import. *)
*)

From Stdlib Require Import Arith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.

(* ===== B-1. affinity_admissibility pointwise spec ===== *)

Lemma affinity_admissibility_spec :
  forall (aff : cpu_affinity) j cpu,
    affinity_admissibility aff j cpu <-> aff j cpu.
Proof.
  intros aff j cpu.
  unfold affinity_admissibility.
  tauto.
Qed.

(* ===== B-2. all_cpus_admissible / singleton specializations ===== *)

Lemma all_cpus_admissible_spec :
  forall j cpu,
    all_cpus_admissible j cpu.
Proof.
  intros j cpu.
  exact I.
Qed.

Lemma singleton_admissibility_spec :
  forall (assign : JobId -> CPU) j cpu,
    singleton_admissibility assign j cpu <-> cpu = assign j.
Proof.
  intros assign j cpu.
  unfold singleton_admissibility.
  split; intros H; symmetry; exact H.
Qed.

(* singleton_admissibility_unique is proved in Admissibility.v. *)
