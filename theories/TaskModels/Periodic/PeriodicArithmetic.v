From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.

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

Lemma nat_div_35q_plus_1_by_7 :
  forall q,
    (35 * q + 1) / 7 = 5 * q.
Proof.
  intro q.
  assert (Hmod : (35 * q + 1) mod 7 = 1).
  {
    replace (35 * q + 1) with (7 * (5 * q) + 1) by lia.
    rewrite Nat.add_mod by lia.
    replace ((7 * (5 * q)) mod 7) with 0.
    2:{
      symmetry.
      rewrite Nat.mul_comm.
      apply nat_mod_mul_left.
      lia.
    }
    simpl.
    reflexivity.
  }
  pose proof (Nat.div_mod (35 * q + 1) 7) as Hdiv.
  assert (Hneq : 7 <> 0) by lia.
  specialize (Hdiv Hneq).
  lia.
Qed.

Lemma nat_mod_35q_plus_1_by_35 :
  forall q,
    (35 * q + 1) mod 35 = 1.
Proof.
  intro q.
  replace (35 * q + 1) with (1 + 35 * q) by lia.
  rewrite Nat.add_mod by lia.
  replace ((35 * q) mod 35) with 0.
  2:{
    symmetry.
    rewrite Nat.mul_comm.
    apply nat_mod_mul_left.
    lia.
  }
  simpl.
  reflexivity.
Qed.

Lemma nat_mod_7k_by_7 :
  forall k,
    (7 * k) mod 7 = 0.
Proof.
  intro k.
  rewrite Nat.mul_comm.
  apply nat_mod_mul_left.
  lia.
Qed.

Lemma nat_mod_5k_by_5 :
  forall k,
    (5 * k) mod 5 = 0.
Proof.
  intro k.
  rewrite Nat.mul_comm.
  apply nat_mod_mul_left.
  lia.
Qed.
