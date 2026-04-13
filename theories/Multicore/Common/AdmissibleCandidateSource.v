(* AdmissibleCandidateSource.v
   Admissibility-aware candidate source specification.

   This file defines AdmissibleCandidateSourceSpec, a derived record that
   extends the existing CandidateSourceSpec with an explicit admissibility
   condition in the completeness field.  The standard CandidateSourceSpec
   requires that every eligible job in the subset J is a candidate;
   AdmissibleCandidateSourceSpec requires only that every eligible AND
   admissible-somewhere job in J is a candidate.

   This weaker (more preconditioned) completeness clause is designed for
   future affinity-aware multicore schedulers where the candidate list may
   be restricted to jobs admissible on the available CPUs.

   Bridge lemmas
   -------------
   candidate_source_spec_to_admissible       : CandidateSourceSpec -> AdmissibleCandidateSourceSpec adm
   singleton_admissibility_candidate_specialization :
     CandidateSourceSpec -> AdmissibleCandidateSourceSpec (singleton_admissibility assign)

   Note: this file lives in Multicore/Common/ (not Abstractions/) because
   AdmissibleCandidateSourceSpec depends on admissible_cpu and
   admissible_somewhere from Multicore.Common.Admissibility, and the
   Abstractions layer must not import Multicore.
*)

From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.

(* ===== AdmissibleCandidateSourceSpec ===== *)

(** A candidate source spec parameterised by an admissibility predicate.

    The completeness clause is weaker than CandidateSourceSpec.candidates_complete:
    it only demands that a job be a candidate when it is eligible AND admissible
    somewhere (under adm).  For all_cpus_admissible this is equivalent to the
    standard completeness (modulo 0 < m); for restricted affinities it lets the
    candidate list omit jobs that cannot run on any available CPU. *)
Record AdmissibleCandidateSourceSpec
    (adm : admissible_cpu)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource) : Prop :=
  mkAdmissibleCandidateSourceSpec {
    admissible_candidates_sound :
      forall jobs m sched t j,
        In j (candidates_of jobs m sched t) -> J j;
    admissible_candidates_complete :
      forall jobs m sched t j,
        J j ->
        eligible jobs m sched j t ->
        admissible_somewhere adm jobs m sched j t ->
        In j (candidates_of jobs m sched t);
    admissible_candidates_prefix_extensional :
      forall jobs m s1 s2 t,
        (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
        candidates_of jobs m s1 t = candidates_of jobs m s2 t
  }.

(* ===== Bridge lemmas ===== *)

(** C-1. CandidateSourceSpec implies AdmissibleCandidateSourceSpec for any adm.

    Proof idea: the admissible_candidates_complete field has an extra
    precondition (admissible_somewhere adm j t) compared to
    CandidateSourceSpec.candidates_complete.  We ignore that extra
    hypothesis and directly invoke the standard completeness, making this
    an easy downward implication. *)
Lemma candidate_source_spec_to_admissible :
  forall adm (J : JobId -> Prop) (candidates_of : CandidateSource),
    CandidateSourceSpec J candidates_of ->
    AdmissibleCandidateSourceSpec adm J candidates_of.
Proof.
  intros adm J candidates_of Hcand.
  destruct Hcand as [Hsound Hcomplete Hext].
  constructor.
  - exact Hsound.
  - intros jobs m sched t j HJ Helig _.
    exact (Hcomplete jobs m sched t j HJ Helig).
  - exact Hext.
Qed.

(** C-2. Specialisation for singleton_admissibility (used in Partitioned
    connection lemmas): direct corollary of C-1. *)
Lemma singleton_admissibility_candidate_specialization :
  forall (assign : JobId -> CPU) (J : JobId -> Prop) (candidates_of : CandidateSource),
    CandidateSourceSpec J candidates_of ->
    AdmissibleCandidateSourceSpec (singleton_admissibility assign) J candidates_of.
Proof.
  intros assign J candidates_of Hcand.
  exact (candidate_source_spec_to_admissible (singleton_admissibility assign) J candidates_of Hcand).
Qed.
