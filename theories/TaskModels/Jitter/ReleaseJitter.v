From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.

Definition within_jitter (nominal actual delta : Time) : Prop :=
  nominal <= actual /\ actual <= nominal + delta.

Definition within_jitter_b (nominal actual delta : Time) : bool :=
  Nat.leb nominal actual && Nat.leb actual (nominal + delta).

Lemma within_jitter_b_spec :
  forall nominal actual delta,
    within_jitter_b nominal actual delta = true <->
    within_jitter nominal actual delta.
Proof.
  intros nominal actual delta.
  unfold within_jitter_b, within_jitter.
  rewrite andb_true_iff, !Nat.leb_le.
  tauto.
Qed.

Lemma within_jitter_implies_lower_bound :
  forall nominal actual delta,
    within_jitter nominal actual delta ->
    nominal <= actual.
Proof.
  intros nominal actual delta [Hlb _].
  exact Hlb.
Qed.

Lemma within_jitter_implies_upper_bound :
  forall nominal actual delta,
    within_jitter nominal actual delta ->
    actual <= nominal + delta.
Proof.
  intros nominal actual delta [_ Hub].
  exact Hub.
Qed.

