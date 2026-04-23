(* GlobalFIFO.v
   Global First-In-First-Out multiprocessor scheduler.
   Wrapper + validity layer over the generic top-m bridge.

   The scheduler interprets candidate-list order as FIFO priority, filters
   duplicate candidates, keeps only eligible jobs, and assigns the first m
   selected jobs to CPUs 0 .. m-1 via nth_error (see TopMSchedulerBridge).

   This file intentionally stops at the wrapper + validity boundary. Unlike
   GlobalEDF.v and GlobalLLF.v, it does not yet add the full admissibility
   wrapper family or schedulability-introduction layer. *)

From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.TopMSchedulerBridgeFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ValidityFacts.
Import ListNotations.

Definition fifo_eligible_candidates
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (candidates : list JobId) : list JobId :=
  filter (fun j => eligibleb jobs m sched j t) (nodup Nat.eq_dec candidates).

Definition choose_top_m_fifo
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (candidates : list JobId) : list JobId :=
  firstn m (fifo_eligible_candidates jobs m sched t candidates).

Lemma in_firstn_sound :
  forall (A : Type) n (xs : list A) x,
    In x (firstn n xs) ->
    In x xs.
Proof.
  intros A n.
  induction n as [|n IH]; intros xs x Hin; simpl in Hin.
  - contradiction.
  - destruct xs as [|y ys]; simpl in *.
    + contradiction.
    + destruct Hin as [-> | Hin].
      * left. reflexivity.
      * right. apply IH. exact Hin.
Qed.

Lemma firstn_preserves_NoDup :
  forall (A : Type) n (xs : list A),
    NoDup xs ->
    NoDup (firstn n xs).
Proof.
  intros A n.
  induction n as [|n IH]; intros xs Hnodup; simpl.
  - constructor.
  - destruct xs as [|x xs]; simpl.
    + constructor.
    + inversion Hnodup as [|x' xs' Hnotin Htail]; subst x' xs'.
      constructor.
      * intro Hin.
        apply Hnotin.
        apply in_firstn_sound in Hin.
        exact Hin.
      * apply IH. exact Htail.
Qed.

Lemma choose_top_m_fifo_nodup :
  forall jobs m sched t candidates,
    NoDup (choose_top_m_fifo jobs m sched t candidates).
Proof.
  intros jobs m sched t candidates.
  unfold choose_top_m_fifo, fifo_eligible_candidates.
  apply firstn_preserves_NoDup.
  apply NoDup_filter.
  apply NoDup_nodup.
Qed.

Lemma choose_top_m_fifo_in_candidates :
  forall jobs m sched t candidates j,
    In j (choose_top_m_fifo jobs m sched t candidates) ->
    In j candidates.
Proof.
  intros jobs m sched t candidates j Hin.
  unfold choose_top_m_fifo, fifo_eligible_candidates in Hin.
  apply in_firstn_sound in Hin.
  apply filter_In in Hin as [Hin _].
  apply nodup_In in Hin.
  exact Hin.
Qed.

Lemma choose_top_m_fifo_eligible :
  forall jobs m sched t candidates j,
    In j (choose_top_m_fifo jobs m sched t candidates) ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hin.
  unfold choose_top_m_fifo, fifo_eligible_candidates in Hin.
  apply in_firstn_sound in Hin.
  apply filter_In in Hin as [_ Helig].
  apply eligibleb_iff.
  exact Helig.
Qed.

Lemma choose_top_m_fifo_length_le_m :
  forall jobs m sched t candidates,
    length (choose_top_m_fifo jobs m sched t candidates) <= m.
Proof.
  intros jobs m sched t candidates.
  unfold choose_top_m_fifo.
  rewrite length_firstn.
  lia.
Qed.

Lemma choose_top_m_fifo_complete_if_room :
  forall jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    ~ In j (choose_top_m_fifo jobs m sched t candidates) ->
    length (choose_top_m_fifo jobs m sched t candidates) = m.
Proof.
  intros jobs m sched t candidates j Hin Helig Hnotin.
  unfold choose_top_m_fifo.
  set (eligible_fifo := fifo_eligible_candidates jobs m sched t candidates).
  change (~ In j (firstn m eligible_fifo)) in Hnotin.
  assert (Hin_fifo : In j eligible_fifo).
  { unfold eligible_fifo, fifo_eligible_candidates.
    apply filter_In.
    split.
    - apply nodup_In. exact Hin.
    - apply eligibleb_iff. exact Helig. }
  assert (~ length eligible_fifo < m) as Hlen.
  { intro Hlt.
    rewrite firstn_all2 in Hnotin by lia.
    apply Hnotin.
    exact Hin_fifo. }
  assert (m <= length eligible_fifo) by lia.
  rewrite length_firstn.
  rewrite Nat.min_l by lia.
  reflexivity.
Qed.

Definition global_fifo_top_m_spec : GenericTopMSchedulingAlgorithm :=
  mkGenericTopMSchedulingAlgorithm
    choose_top_m_fifo
    choose_top_m_fifo_nodup
    choose_top_m_fifo_in_candidates
    choose_top_m_fifo_eligible
    choose_top_m_fifo_length_le_m
    choose_top_m_fifo_complete_if_room.

Definition global_fifo_scheduler
    (candidates_of : CandidateSource) : Scheduler :=
  top_m_algorithm_schedule global_fifo_top_m_spec candidates_of.

Definition global_fifo_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (_ : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  global_fifo_scheduler candidates_of.

Lemma global_fifo_eq_cpu :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    sched t c =
      if c <? m then
        nth_error (choose_top_m global_fifo_top_m_spec jobs m sched t
                     (candidates_of jobs m sched t)) c
      else None.
Proof.
  intros candidates_of jobs m sched t c Hrel.
  exact (top_m_algorithm_eq_cpu
           global_fifo_top_m_spec candidates_of jobs m sched t c Hrel).
Qed.

Lemma global_fifo_valid :
  forall candidates_of jobs m sched,
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    valid_schedule jobs m sched.
Proof.
  intros candidates_of jobs m sched Hrel.
  exact (top_m_algorithm_valid
           global_fifo_top_m_spec candidates_of jobs m sched Hrel).
Qed.

Lemma global_fifo_idle_outside_range :
  forall candidates_of jobs m sched t c,
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    m <= c ->
    sched t c = None.
Proof.
  intros candidates_of jobs m sched t c Hrel Hge.
  exact (top_m_algorithm_idle_outside_range
           global_fifo_top_m_spec candidates_of jobs m sched t c Hrel Hge).
Qed.

Lemma global_fifo_no_duplication :
  forall candidates_of jobs m sched,
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    no_duplication m sched.
Proof.
  intros candidates_of jobs m sched Hrel.
  exact (top_m_algorithm_no_duplication
           global_fifo_top_m_spec candidates_of jobs m sched Hrel).
Qed.

Lemma global_fifo_semantic_validity :
  forall candidates_of jobs m sched,
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    multicore_semantic_validity jobs m sched.
Proof.
  intros candidates_of jobs m sched Hrel.
  exact (top_m_algorithm_semantic_validity
           global_fifo_top_m_spec candidates_of jobs m sched Hrel).
Qed.

Lemma global_fifo_in_subset :
  forall J candidates_of jobs m sched t c j,
    CandidateSourceSpec J candidates_of ->
    scheduler_rel (global_fifo_scheduler candidates_of) jobs m sched ->
    c < m ->
    sched t c = Some j ->
    J j.
Proof.
  intros J candidates_of jobs m sched t c j Hcand Hrel Hlt Hrun.
  exact (top_m_algorithm_in_subset
           J global_fifo_top_m_spec candidates_of jobs m sched t c j
           Hcand Hrel Hlt Hrun).
Qed.
