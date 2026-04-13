From Stdlib Require Import List Bool Arith Arith.PeanoNat Classical.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Lemmas.
Import ListNotations.

(* Lemmas derived from GenericSchedulingAlgorithm that require classical logic.
   Kept separate from SchedulingAlgorithmLemmas.v so the constructive core remains
   Classical-free. *)

Section SchedulingAlgorithmClassicalLemmasSection.

  Variable spec        : GenericSchedulingAlgorithm.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* E3: if choose returns None, each candidate is either unreleased or completed.
     (eligible = released AND NOT completed;
      NOT eligible means NOT released OR completed.) *)
  Lemma choose_none_implies_each_candidate_unreleased_or_completed :
      spec.(choose) jobs m sched t candidates = None ->
      forall j, In j candidates ->
        ~released jobs j t \/ completed jobs m sched j t.
  Proof.
    intros Hnone j Hin.
    pose proof (choose_none_implies_no_eligible spec jobs m sched t candidates Hnone j Hin) as Hnelig.
    unfold eligible in Hnelig.
    destruct (classic (released jobs j t)) as [Hrel | Hnrel].
    - right. apply NNPP. intro Hnc. apply Hnelig.
      split. exact Hrel. exact Hnc.
    - left. exact Hnrel.
  Qed.

End SchedulingAlgorithmClassicalLemmasSection.
