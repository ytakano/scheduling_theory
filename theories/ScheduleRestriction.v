From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleTransform.
Import ListNotations.

(* ===== Section 1: single-CPU invariant ===== *)

(* Predicate: all CPUs except 0 are idle. *)
Definition single_cpu_only (sched : Schedule) : Prop :=
  forall t c, 0 < c -> sched t c = None.

(* Build a single-CPU-only schedule from any schedule. *)
Definition mk_single_cpu (sched : Schedule) : Schedule :=
  fun t c => if c =? 0 then sched t 0 else None.

Lemma mk_single_cpu_cpu0 : forall sched t,
    mk_single_cpu sched t 0 = sched t 0.
Proof.
  intros sched t. unfold mk_single_cpu. simpl. reflexivity.
Qed.

Lemma mk_single_cpu_other : forall sched t c,
    0 < c -> mk_single_cpu sched t c = None.
Proof.
  intros sched t c Hc. unfold mk_single_cpu.
  destruct (c =? 0) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
Qed.

Lemma mk_single_cpu_only : forall sched,
    single_cpu_only (mk_single_cpu sched).
Proof.
  intros sched t c Hc. exact (mk_single_cpu_other sched t c Hc).
Qed.

Lemma mk_single_cpu_service : forall sched j T,
    service_job 1 (mk_single_cpu sched) j T = service_job 1 sched j T.
Proof.
  intros sched j T.
  apply service_job_eq_of_cpu_count_eq.
  intros t _. simpl. unfold runs_on. rewrite mk_single_cpu_cpu0. reflexivity.
Qed.

Lemma mk_single_cpu_valid : forall jobs sched,
    valid_schedule jobs 1 sched ->
    valid_schedule jobs 1 (mk_single_cpu sched).
Proof.
  intros jobs sched Hvalid j t c Hc Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  rewrite mk_single_cpu_cpu0 in Hrun.
  assert (Helig : eligible jobs 1 sched j t) by exact (Hvalid j t 0 Hc Hrun).
  split.
  - exact (proj1 Helig).
  - intro Hcomp. apply (proj2 Helig). unfold completed in *.
    rewrite mk_single_cpu_service in Hcomp. exact Hcomp.
Qed.

Lemma mk_single_cpu_feasible : forall J jobs sched,
    feasible_schedule_on J jobs 1 sched ->
    feasible_schedule_on J jobs 1 (mk_single_cpu sched).
Proof.
  intros J jobs sched Hfeas j HJj Hmiss.
  apply (Hfeas j HJj).
  unfold missed_deadline in *. unfold completed in *.
  rewrite <- mk_single_cpu_service. exact Hmiss.
Qed.

(* single_cpu_only is preserved by swap_at. *)
Lemma swap_at_single_cpu_only : forall sched t1 t2,
    single_cpu_only sched ->
    single_cpu_only (swap_at sched t1 t2).
Proof.
  intros sched t1 t2 Honly t c Hc.
  assert (Hcne : c <> 0) by lia.
  rewrite (swap_at_same_outside sched t1 t2 t c (or_introl Hcne)).
  exact (Honly t c Hc).
Qed.

(* ===== Section 2: J-restriction ===== *)

(* Restrict to J-jobs on CPU 0 only. *)
Definition J_restrict (J_bool : JobId -> bool) (sched : Schedule) : Schedule :=
  fun t c =>
    if c =? 0 then
      match sched t 0 with
      | Some j => if J_bool j then Some j else None
      | None => None
      end
    else None.

Lemma J_restrict_cpu0 : forall J_bool sched t,
    J_restrict J_bool sched t 0 =
    match sched t 0 with
    | Some j => if J_bool j then Some j else None
    | None => None
    end.
Proof.
  intros. unfold J_restrict. simpl. reflexivity.
Qed.

Lemma J_restrict_other : forall J_bool sched t c,
    0 < c -> J_restrict J_bool sched t c = None.
Proof.
  intros J_bool sched t c Hc. unfold J_restrict.
  destruct (c =? 0) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
Qed.

Lemma J_restrict_only : forall J_bool sched,
    single_cpu_only (J_restrict J_bool sched).
Proof.
  intros J_bool sched t c Hc. exact (J_restrict_other J_bool sched t c Hc).
Qed.

Lemma J_restrict_J_only : forall J_bool J sched t j,
    (forall x, J_bool x = true <-> J x) ->
    J_restrict J_bool sched t 0 = Some j ->
    J j.
Proof.
  intros J_bool J sched t j HJbool Hrun.
  rewrite J_restrict_cpu0 in Hrun.
  destruct (sched t 0) as [j'|] eqn:Ht0.
  - destruct (J_bool j') eqn:EJj'.
    + injection Hrun as Heq. subst j'. apply HJbool. exact EJj'.
    + discriminate.
  - discriminate.
Qed.

Lemma J_restrict_service_J : forall J_bool J sched j T,
    (forall x, J_bool x = true <-> J x) ->
    J j ->
    service_job 1 (J_restrict J_bool sched) j T = service_job 1 sched j T.
Proof.
  intros J_bool J sched j T HJbool HJj.
  assert (Hj_bool : J_bool j = true) by (apply HJbool; exact HJj).
  apply service_job_eq_of_cpu_count_eq.
  intros t _.
  destruct (sched t 0) as [j'|] eqn:Ht0.
  - destruct (J_bool j') eqn:EJj'.
    + assert (HJR : J_restrict J_bool sched t 0 = Some j').
      { rewrite J_restrict_cpu0. rewrite Ht0. rewrite EJj'. reflexivity. }
      destruct (Nat.eq_dec j j') as [-> | Hne].
      * rewrite (cpu_count_1_some_eq (J_restrict J_bool sched) j' t HJR).
        symmetry. exact (cpu_count_1_some_eq sched j' t Ht0).
      * rewrite (cpu_count_1_some_neq (J_restrict J_bool sched) j j' t HJR Hne).
        symmetry. exact (cpu_count_1_some_neq sched j j' t Ht0 Hne).
    + assert (HJR : J_restrict J_bool sched t 0 = None).
      { rewrite J_restrict_cpu0. rewrite Ht0. rewrite EJj'. reflexivity. }
      assert (Hne : j <> j').
      { intro Heq. subst j'. rewrite Hj_bool in EJj'. discriminate. }
      rewrite (cpu_count_1_none (J_restrict J_bool sched) j t HJR).
      symmetry. exact (cpu_count_1_some_neq sched j j' t Ht0 Hne).
  - assert (HJR : J_restrict J_bool sched t 0 = None).
    { rewrite J_restrict_cpu0. rewrite Ht0. reflexivity. }
    rewrite (cpu_count_1_none (J_restrict J_bool sched) j t HJR).
    symmetry. exact (cpu_count_1_none sched j t Ht0).
Qed.

Lemma J_restrict_valid : forall J_bool J jobs sched,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    valid_schedule jobs 1 (J_restrict J_bool sched).
Proof.
  intros J_bool J jobs sched HJbool Hvalid j t c Hc Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  rewrite J_restrict_cpu0 in Hrun.
  destruct (sched t 0) as [j'|] eqn:Ht0.
  - destruct (J_bool j') eqn:EJj'.
    + injection Hrun as Heq. subst j'.
      assert (HJj : J j) by (apply HJbool; exact EJj').
      assert (Helig : eligible jobs 1 sched j t) by exact (Hvalid j t 0 Hc Ht0).
      split.
      * exact (proj1 Helig).
      * intro Hcomp. apply (proj2 Helig). unfold completed in *.
        rewrite (J_restrict_service_J J_bool J sched j _ HJbool HJj) in Hcomp.
        exact Hcomp.
    + discriminate.
  - discriminate.
Qed.

Lemma J_restrict_feasible : forall J_bool J jobs sched,
    (forall x, J_bool x = true <-> J x) ->
    feasible_schedule_on J jobs 1 sched ->
    feasible_schedule_on J jobs 1 (J_restrict J_bool sched).
Proof.
  intros J_bool J jobs sched HJbool Hfeas j HJj Hmiss.
  apply (Hfeas j HJj).
  unfold missed_deadline in *. unfold completed in *.
  rewrite <- (J_restrict_service_J J_bool J sched j _ HJbool HJj). exact Hmiss.
Qed.
