From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.SchedulingAlgorithmNormalization.

Fixpoint generated_schedule_prefix
    (alg : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (H : Time) : Schedule :=
  match H with
  | 0 => fun _ _ => None
  | S H' =>
      let pref := generated_schedule_prefix alg candidates_of jobs H' in
      fun t c =>
        if Nat.ltb t H' then pref t c else
        if Nat.eqb t H' then
          if Nat.eqb c 0
          then choose alg jobs 1 pref H' (candidates_of jobs 1 pref H')
          else None
        else None
  end.

Definition generated_schedule
    (alg : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job) : Schedule :=
  fun t c => generated_schedule_prefix alg candidates_of jobs (S t) t c.

Lemma generated_schedule_prefix_stable :
  forall alg candidates_of jobs H t c,
    t < H ->
    generated_schedule_prefix alg candidates_of jobs H t c =
    generated_schedule alg candidates_of jobs t c.
Proof.
  intros alg candidates_of jobs H.
  induction H as [|H' IH]; intros t c Hlt.
  - lia.
  - simpl.
    destruct (Nat.eq_dec t H') as [-> | Hneq].
    + unfold generated_schedule.
      reflexivity.
    + assert (t < H') by lia.
      destruct (Nat.ltb t H') eqn:Hcmp.
      * apply IH.
        lia.
      * apply Nat.ltb_ge in Hcmp.
        lia.
Qed.

Lemma generated_schedule_prefix_agrees_before :
  forall alg candidates_of jobs H,
    agrees_before
      (generated_schedule_prefix alg candidates_of jobs H)
      (generated_schedule alg candidates_of jobs)
      H.
Proof.
  intros alg candidates_of jobs H t c Hlt.
  apply generated_schedule_prefix_stable.
  exact Hlt.
Qed.

Lemma generated_schedule_eq_cpu0_with_prefix :
  forall alg candidates_of jobs t,
    generated_schedule alg candidates_of jobs t 0 =
    choose alg jobs 1
      (generated_schedule_prefix alg candidates_of jobs t)
      t
      (candidates_of jobs 1
         (generated_schedule_prefix alg candidates_of jobs t) t).
Proof.
  intros alg candidates_of jobs t.
  unfold generated_schedule.
  simpl.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma generated_schedule_other_cpu_idle :
  forall alg candidates_of jobs t c,
    0 < c ->
    generated_schedule alg candidates_of jobs t c = None.
Proof.
  intros alg candidates_of jobs t c Hc.
  unfold generated_schedule.
  simpl.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.eqb_refl.
  destruct (Nat.eqb_spec c 0) as [Heq | Hneq].
  - lia.
  - reflexivity.
Qed.

Theorem generated_schedule_scheduler_rel :
  forall alg J
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    ChooseAgreesBefore alg jobs candidates_of ->
    scheduler_rel
      (single_cpu_algorithm_schedule alg candidates_of)
      jobs 1
      (generated_schedule alg candidates_of jobs).
Proof.
  intros alg J candidates_of cand_spec jobs Hchoose.
  unfold single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + rewrite generated_schedule_eq_cpu0_with_prefix.
      rewrite (Hchoose
                 (generated_schedule_prefix alg candidates_of jobs t)
                 (generated_schedule alg candidates_of jobs)
                 t).
      * reflexivity.
      * apply generated_schedule_prefix_agrees_before.
    + intros c Hc.
      apply generated_schedule_other_cpu_idle.
      exact Hc.
Qed.
