From Stdlib Require Import Arith Arith.PeanoNat List Bool.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Multicore.Partitioned.Partitioned.

(* Fully constructive: no Classical import. *)

(** * Partitioned Bool Lemmas

    Policy-independent bool reflection for [local_jobset].
    Shared by all partitioned policy wrappers (EDF, LLF, FIFO, RR, ...). *)

(** Boolean membership test for the local job set of CPU [c].
    [local_jobset_bool assign J_bool c j] is true when [J_bool j] holds
    and [j] is assigned to [c]. *)
Definition local_jobset_bool
    (assign : JobId -> CPU)
    (J_bool : JobId -> bool)
    (c : CPU) : JobId -> bool :=
  fun j => andb (J_bool j) (Nat.eqb (assign j) c).

(** Correctness of [local_jobset_bool]: given that [J_bool] reflects [J],
    [local_jobset_bool assign J_bool c] reflects [local_jobset assign J c]. *)
Lemma local_jobset_bool_spec :
    forall (assign : JobId -> CPU)
           (J : JobId -> Prop)
           (J_bool : JobId -> bool)
           c,
      (forall x, J_bool x = true <-> J x) ->
      forall x,
        local_jobset_bool assign J_bool c x = true <->
        local_jobset assign J c x.
Proof.
  intros assign J J_bool c HJbool x.
  unfold local_jobset_bool, local_jobset.
  split.
  - intro Hx.
    apply andb_prop in Hx.
    destruct Hx as [HJx Hassign].
    apply Nat.eqb_eq in Hassign.
    apply HJbool in HJx.
    tauto.
  - intros [HJx Hassign].
    apply <- HJbool in HJx.
    apply Nat.eqb_eq in Hassign.
    rewrite HJx, Hassign.
    reflexivity.
Qed.
