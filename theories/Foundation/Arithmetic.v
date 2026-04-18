From Stdlib Require Import Arith Arith.PeanoNat Lia.

(* Small Nat facts that are independent of any scheduling model and can be
   reused across task-model and analysis layers. *)

Lemma nat_div2_double :
  forall k,
    Nat.div2 (2 * k) = k.
Proof.
  intro k.
  exact (Nat.div2_double k).
Qed.

Lemma nat_div2_succ_double :
  forall k,
    Nat.div2 (S (2 * k)) = k.
Proof.
  intro k.
  exact (Nat.div2_succ_double k).
Qed.

Lemma nat_div_mul_exact :
  forall a b,
    0 < b ->
    (a * b) / b = a.
Proof.
  intros a b Hb.
  apply Nat.div_mul.
  lia.
Qed.

Lemma nat_mod_mul_left :
  forall a b,
    0 < b ->
    (a * b) mod b = 0.
Proof.
  intros a b Hb.
  apply Nat.mod_mul.
  lia.
Qed.
