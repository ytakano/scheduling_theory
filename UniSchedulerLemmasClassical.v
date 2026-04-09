From Stdlib Require Import List Bool Arith Arith.PeanoNat Classical.
Require Import Base.
Require Import Schedule.
Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.
Import ListNotations.

(* Lemmas derived from GenericSchedulerDecisionSpec that require classical logic.
   Kept separate from UniSchedulerLemmas.v so the constructive core remains
   Classical-free. *)

Section UniSchedulerLemmasClassicalSection.

  Variable spec        : GenericSchedulerDecisionSpec.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* E3: if choose returns None, each candidate is either unreleased, completed,
     or currently running on some CPU.
     (ready = eligible AND NOT running = (released AND NOT completed) AND NOT running,
      NOT ready means NOT eligible OR running, i.e., unreleased OR completed OR running.) *)
  Lemma choose_none_implies_each_candidate_unreleased_or_completed :
      spec.(choose_g) jobs m sched t candidates = None ->
      forall j, In j candidates ->
        ~released jobs j t \/ completed jobs m sched j t \/ running m sched j t.
  Proof.
    intros Hnone j Hin.
    pose proof (choose_none_implies_no_ready spec jobs m sched t candidates Hnone j Hin) as Hnready.
    unfold ready, eligible in Hnready.
    destruct (classic (released jobs j t)) as [Hrel | Hnrel].
    - destruct (classic (running m sched j t)) as [Hrun | Hnrun].
      + right. right. exact Hrun.
      + right. left. apply NNPP. intro Hnc. apply Hnready.
        split. split. exact Hrel. exact Hnc. exact Hnrun.
    - left. exact Hnrel.
  Qed.

End UniSchedulerLemmasClassicalSection.
