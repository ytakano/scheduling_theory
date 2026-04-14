From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.

Import ListNotations.

(* ===== Ceiling-division arithmetic ===== *)

(* k * p < H ∧ p ≥ 1  →  k < ⌈H/p⌉   where ⌈H/p⌉ = (H + p - 1) / p *)
Lemma nat_mul_lt_ceil_div :
  forall k H p,
    1 <= p ->
    k * p < H ->
    k < (H + p - 1) / p.
Proof.
  intros k H p Hp Hlt.
  assert (Hp0 : p <> 0) by lia.
  assert (Hp' : 0 < p) by lia.
  destruct (Nat.lt_ge_cases k ((H + p - 1) / p)) as [Hlt' | Hge].
  - exact Hlt'.
  - exfalso.
    (* Hge : (H + p - 1) / p <= k *)
    assert (Hmul : (H + p - 1) / p * p <= k * p)
      by (apply Nat.mul_le_mono_r; exact Hge).
    pose proof (Nat.div_mod (H + p - 1) p Hp0) as Hmod.
    (* Hmod : H + p - 1 = p * ((H+p-1)/p) + (H+p-1) mod p *)
    pose proof (Nat.mod_upper_bound (H + p - 1) p Hp0) as Hlt2.
    nia.
Qed.

(* Monotonicity of ceiling division. *)
Lemma ceil_div_mono :
  forall H1 H2 p,
    H1 <= H2 ->
    (H1 + p - 1) / p <= (H2 + p - 1) / p.
Proof.
  intros H1 H2 p Hle.
  apply Nat.Div0.div_le_mono.
  lia.
Qed.

(* ===== Workload aggregation ===== *)

(* Total execution demand of a list of jobs. *)
Fixpoint total_job_cost
    (jobs : JobId -> Job) (l : list JobId) : nat :=
  match l with
  | [] => 0
  | j :: l' => job_cost (jobs j) + total_job_cost jobs l'
  end.

(* A list's total cost is bounded by its length times the per-job cost cap. *)
Lemma total_job_cost_le_length_mul :
  forall jobs l c,
    (forall j, In j l -> job_cost (jobs j) <= c) ->
    total_job_cost jobs l <= length l * c.
Proof.
  intros jobs l c Hcost.
  induction l as [|j l IH]; simpl.
  - lia.
  - assert (Hhead : job_cost (jobs j) <= c).
    { apply Hcost. now left. }
    assert (Htail : forall j', In j' l -> job_cost (jobs j') <= c).
    { intros j' Hj'. apply Hcost. now right. }
    specialize (IH Htail).
    lia.
Qed.
