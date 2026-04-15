From Stdlib Require Import List Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.TopMMetricChooser.
From RocqSched Require Import Uniprocessor.Policies.Common.MetricChooser.
Import ListNotations.

Lemma choose_top_m_by_metric_excluded_eligible_implies_full :
  forall k metric jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    ~ In j (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    length (choose_top_m_by_metric k metric jobs m sched t candidates) = k.
Proof.
  intros k metric jobs m sched t candidates j Hin Helig Hnotin.
  eapply choose_top_m_by_metric_complete_if_room; eauto.
Qed.

Lemma choose_top_m_by_metric_member_le_excluded_eligible :
  forall k metric jobs m sched t candidates j_run j,
    In j_run (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    In j candidates ->
    eligible jobs m sched j t ->
    ~ In j (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    (metric j_run <= metric j)%Z.
Proof.
  induction k as [|k' IH]; intros metric jobs m sched t candidates j_run j
    Hrun Hin Helig Hnotin.
  - simpl in Hrun. contradiction.
  - simpl in Hrun, Hnotin.
    destruct (choose_min_metric metric jobs m sched t candidates) as [best|] eqn:Hbest.
    + destruct Hrun as [<- | Htail].
      * eapply choose_min_metric_min; eauto.
      * destruct (Nat.eq_dec j best) as [-> | Hneq].
        { exfalso. apply Hnotin. left. reflexivity. }
        eapply IH.
        -- exact Htail.
        -- exact (@in_in_remove _ Nat.eq_dec candidates j best Hneq Hin).
        -- exact Helig.
        -- intro Hin_tail. apply Hnotin. right. exact Hin_tail.
    + exfalso.
      assert (Hexists : exists j', In j' candidates /\ eligible jobs m sched j' t).
      { exists j. split; assumption. }
      destruct (choose_min_metric_some_if_exists metric jobs m sched t candidates Hexists)
        as [j' Hsome].
      rewrite Hsome in Hbest. discriminate.
Qed.
