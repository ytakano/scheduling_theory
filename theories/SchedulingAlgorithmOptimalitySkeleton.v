From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import ScheduleLemmas.ScheduleRestriction.
Require Import ScheduleLemmas.ScheduleTruncation.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import SchedulingAlgorithmCanonicalBridge.
Require Import SchedulingAlgorithmNormalization.
Import ListNotations.

Lemma finite_J_restricted_schedule :
  forall J (J_bool : JobId -> bool) jobs,
    (forall x, J_bool x = true <-> J x) ->
    feasible_on J jobs 1 ->
    exists sched1,
      valid_schedule jobs 1 sched1 /\
      feasible_schedule_on J jobs 1 sched1 /\
      (forall t j, sched1 t 0 = Some j -> J j) /\
      single_cpu_only sched1.
Proof.
  intros J J_bool jobs HJbool [sched0 [Hvalid0 Hfeas0]].
  exists (J_restrict J_bool (mk_single_cpu sched0)).
  refine (conj _ (conj _ (conj _ _))).
  - apply (J_restrict_valid J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_valid jobs sched0 Hvalid0).
  - apply (J_restrict_feasible J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_feasible J jobs sched0 Hfeas0).
  - intros t j Hrun.
    exact (J_restrict_J_only J_bool J (mk_single_cpu sched0) t j HJbool Hrun).
  - exact (J_restrict_only J_bool (mk_single_cpu sched0)).
Qed.

Lemma finite_normalized_schedule :
  forall alg J candidates_of jobs sched1 H,
    (forall sched0 H0,
        valid_schedule jobs 1 sched0 ->
        feasible_schedule_on J jobs 1 sched0 ->
        (forall t j, sched0 t 0 = Some j -> J j) ->
        single_cpu_only sched0 ->
        exists sched',
          valid_schedule jobs 1 sched' /\
          feasible_schedule_on J jobs 1 sched' /\
          (forall t j, sched' t 0 = Some j -> J j) /\
          single_cpu_only sched' /\
          matches_dispatch_before alg jobs candidates_of sched' H0) ->
    valid_schedule jobs 1 sched1 ->
    feasible_schedule_on J jobs 1 sched1 ->
    (forall t j, sched1 t 0 = Some j -> J j) ->
    single_cpu_only sched1 ->
    exists sched2,
      valid_schedule jobs 1 sched2 /\
      feasible_schedule_on J jobs 1 sched2 /\
      (forall t j, sched2 t 0 = Some j -> J j) /\
      single_cpu_only sched2 /\
      matches_dispatch_before alg jobs candidates_of sched2 H.
Proof.
  intros alg J candidates_of jobs sched1 H Hnorm Hvalid1 Hfeas1 HJonly1 Hcpu1.
  exact (Hnorm sched1 H Hvalid1 Hfeas1 HJonly1 Hcpu1).
Qed.

Lemma finite_truncated_schedule :
  forall alg J enumJ candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched2,
    DispatchAgreesBefore alg jobs candidates_of ->
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched2 ->
    feasible_schedule_on J jobs 1 sched2 ->
    single_cpu_only sched2 ->
    matches_dispatch_before alg jobs candidates_of sched2 (deadline_horizon jobs enumJ) ->
    exists sched3,
      valid_schedule jobs 1 sched3 /\
      feasible_schedule_on J jobs 1 sched3 /\
      single_cpu_only sched3 /\
      matches_dispatch_before alg jobs candidates_of sched3 (deadline_horizon jobs enumJ) /\
      (forall t, deadline_horizon jobs enumJ <= t -> sched3 t 0 = None).
Proof.
  intros alg J enumJ candidates_of cand_spec jobs sched2 Hdispatch HJ_in
         Hvalid2 Hfeas2 Hcpu2 Hcanon2.
  exists (trunc_sched sched2 (deadline_horizon jobs enumJ)).
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact (trunc_sched_valid jobs sched2 (deadline_horizon jobs enumJ) Hvalid2).
  - apply (trunc_sched_feasible J jobs sched2 (deadline_horizon jobs enumJ) Hfeas2).
    intros j HJj.
    exact (J_implies_deadline_le_horizon J enumJ jobs j HJ_in HJj).
  - exact (trunc_sched_single_cpu_only sched2 (deadline_horizon jobs enumJ) Hcpu2).
  - eapply trunc_sched_preserves_canonical_before; eauto.
  - intros t Hle.
    exact (trunc_sched_after sched2 (deadline_horizon jobs enumJ) t 0 Hle).
Qed.

Lemma finite_canonical_schedule_yields_scheduler_rel :
  forall alg J enumJ candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched3,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched3 ->
    feasible_schedule_on J jobs 1 sched3 ->
    single_cpu_only sched3 ->
    matches_dispatch_before alg jobs candidates_of sched3 (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched3 t 0 = None) ->
    scheduler_rel (single_cpu_algorithm_schedule alg candidates_of) jobs 1 sched3.
Proof.
  intros alg J enumJ candidates_of cand_spec jobs sched3
         HJ_in Hvalid3 Hfeas3 Hcpu3 Hcanon3 Hidle3.
  eapply canonical_and_idle_implies_scheduler_rel_generic; eauto.
Qed.

(* The finite optimality skeleton depends on four reusable ingredients:
   - a feasible witness restricted to the designated job set
   - a normalization routine that produces a canonical prefix
   - DispatchAgreesBefore, combining candidate prefix extensionality with the
     policy-specific chooser invariance
   - truncation to the finite deadline horizon followed by the generic bridge
     from canonical schedules to scheduler_rel *)
Theorem finite_optimality_via_normalization :
  forall alg J (J_bool : JobId -> bool) enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall sched0 H,
        valid_schedule jobs 1 sched0 ->
        feasible_schedule_on J jobs 1 sched0 ->
        (forall t j, sched0 t 0 = Some j -> J j) ->
        single_cpu_only sched0 ->
        exists sched',
          valid_schedule jobs 1 sched' /\
          feasible_schedule_on J jobs 1 sched' /\
          (forall t j, sched' t 0 = Some j -> J j) /\
          single_cpu_only sched' /\
          matches_dispatch_before alg jobs candidates_of sched' H) ->
    DispatchAgreesBefore alg jobs candidates_of ->
    feasible_on J jobs 1 ->
    schedulable_by_on
      J
      (single_cpu_algorithm_scheduler_on J alg candidates_of cand_spec)
      jobs 1.
Proof.
  intros alg J J_bool enumJ candidates_of cand_spec jobs
         HJbool HJ_in Hnorm Hdispatch Hfeas_on.
  destruct (finite_J_restricted_schedule J J_bool jobs HJbool Hfeas_on)
    as [sched1 [Hvalid1 [Hfeas1 [HJonly1 Hcpu1]]]].
  destruct (finite_normalized_schedule alg J candidates_of jobs sched1
              (deadline_horizon jobs enumJ) Hnorm Hvalid1 Hfeas1 HJonly1 Hcpu1)
    as [sched2 [Hvalid2 [Hfeas2 [HJonly2 [Hcpu2 Hcanon2]]]]].
  destruct (finite_truncated_schedule alg J enumJ candidates_of cand_spec jobs sched2
              Hdispatch HJ_in Hvalid2 Hfeas2 Hcpu2 Hcanon2)
    as [sched3 [Hvalid3 [Hfeas3 [Hcpu3 [Hcanon3 Hidle3]]]]].
  assert (Hrel :
            scheduler_rel (single_cpu_algorithm_schedule alg candidates_of) jobs 1 sched3).
  { eapply finite_canonical_schedule_yields_scheduler_rel; eauto. }
  exact (single_cpu_algorithm_schedulable_by_on_intro
           J alg candidates_of cand_spec jobs sched3 Hrel Hfeas3).
Qed.
