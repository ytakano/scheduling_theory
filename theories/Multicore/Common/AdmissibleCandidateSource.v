(* AdmissibleCandidateSource.v
   Admissibility-aware candidate source specification.

   This file fixes the dependency direction between the public candidate-source
   interfaces used by the multicore top-m theorem layer.

   Public boundary hierarchy
   -------------------------
   CandidateSourceSpec
     Canonical subset/eligibility-facing boundary.

   AdmissibleCandidateSourceSpec
     Weaker completeness: only subset jobs that are both eligible and
     admissible somewhere must appear in the candidate list.

   StrongAdmissibleCandidateSourceSpec
     Extends AdmissibleCandidateSourceSpec with the reverse direction needed
     to conclude that every running candidate is admissible somewhere.

   As a consequence:
   - CandidateSourceSpec always weakens to AdmissibleCandidateSourceSpec.
   - StrongAdmissibleCandidateSourceSpec projects to AdmissibleCandidateSourceSpec.
   - A generic theorem of the form
       top_m_selected_from (subset_admissible_somewhere_at ...)
     requires the strong spec, not just the admissible one.

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

Lemma candidate_source_spec_weaken_to_admissible :
  forall adm (J : JobId -> Prop) (candidates_of : CandidateSource),
    CandidateSourceSpec J candidates_of ->
    AdmissibleCandidateSourceSpec adm J candidates_of.
Proof.
  exact candidate_source_spec_to_admissible.
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

(* ===== StrongAdmissibleCandidateSourceSpec ===== *)

(** A stronger variant of AdmissibleCandidateSourceSpec that additionally
    requires every candidate to be admissible somewhere.  This extra field
    makes it possible to prove the general version of
    all_cpus_idle_if_no_subset_admissible_somewhere for arbitrary adm. *)
Record StrongAdmissibleCandidateSourceSpec
    (adm : admissible_cpu)
    (J : JobId -> Prop)
    (candidates_of : CandidateSource) : Prop :=
  mkStrongAdmissibleCandidateSourceSpec {
    strong_admissible_base :
      AdmissibleCandidateSourceSpec adm J candidates_of;
    strong_admissible_candidates_somewhere :
      forall jobs m sched t j,
        In j (candidates_of jobs m sched t) ->
        admissible_somewhere adm jobs m sched j t
  }.

Lemma strong_admissible_base_proj :
  forall adm J candidates_of,
    StrongAdmissibleCandidateSourceSpec adm J candidates_of ->
    AdmissibleCandidateSourceSpec adm J candidates_of.
Proof.
  intros adm J candidates_of H.
  exact (strong_admissible_base _ _ _ H).
Qed.

Lemma strong_admissible_candidate_source_base :
  forall adm J candidates_of,
    StrongAdmissibleCandidateSourceSpec adm J candidates_of ->
    AdmissibleCandidateSourceSpec adm J candidates_of.
Proof.
  exact strong_admissible_base_proj.
Qed.
