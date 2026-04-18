From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.

Definition trunc_sched (sched : Schedule) (H : nat) : Schedule :=
  fun t c => if t <? H then sched t c else None.

Lemma trunc_sched_before :
  forall sched H t c,
    t < H ->
    trunc_sched sched H t c = sched t c.
Proof.
  intros sched H t c Hlt.
  unfold trunc_sched.
  assert (Hltb : (t <? H) = true) by (apply Nat.ltb_lt; exact Hlt).
  now rewrite Hltb.
Qed.

Lemma trunc_sched_after :
  forall sched H t c,
    H <= t ->
    trunc_sched sched H t c = None.
Proof.
  intros sched H t c Hle.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Lemma trunc_sched_agrees_before :
  forall sched H,
    agrees_before (trunc_sched sched H) sched H.
Proof.
  intros sched H t c Hlt.
  apply trunc_sched_before.
  exact Hlt.
Qed.
