From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import UniPolicies.EDF.
Require Import UniPolicies.EDFLemmas.
Import ListNotations.

(* ===== Phase 1: 有限 horizon を job 集合から作る ===== *)

(* The finite time horizon: one past the maximum absolute deadline in enumJ.
   Any job in enumJ has deadline strictly less than this value. *)
Definition deadline_horizon
    (jobs : JobId -> Job)
    (enumJ : list JobId) : nat :=
  S (fold_right Nat.max 0 (map (fun j => job_abs_deadline (jobs j)) enumJ)).

(* Helper: every element of a list is <= fold_right Nat.max 0 of that list. *)
Lemma fold_right_max_upper_bound :
  forall (l : list nat) (x : nat),
    In x l ->
    x <= fold_right Nat.max 0 l.
Proof.
  intros l x Hin.
  induction l as [| h rest IH].
  - contradiction.
  - simpl. destruct Hin as [-> | Hin'].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 rest).
      * apply IH. exact Hin'.
      * apply Nat.le_max_r.
Qed.

(* Any job in enumJ has deadline strictly less than deadline_horizon. *)
Lemma in_enum_implies_deadline_lt_horizon :
  forall jobs enumJ j,
    In j enumJ ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros jobs enumJ j Hin.
  unfold deadline_horizon.
  apply Nat.lt_succ_r.
  apply fold_right_max_upper_bound.
  exact (in_map (fun j0 => job_abs_deadline (jobs j0)) enumJ j Hin).
Qed.

(* Any job in J has deadline strictly less than deadline_horizon,
   provided enumJ is a complete enumeration of J. *)
Lemma J_implies_deadline_lt_horizon :
  forall J enumJ jobs j,
    (forall j, J j -> In j enumJ) ->
    J j ->
    job_abs_deadline (jobs j) < deadline_horizon jobs enumJ.
Proof.
  intros J enumJ jobs j Hcomplete HJj.
  apply in_enum_implies_deadline_lt_horizon.
  apply Hcomplete. exact HJj.
Qed.

(* ===== Phase 2: repair 対象の 2 時刻を固定する ===== *)

(* 4. first_violation_has_repair_witness:
   EDF violation at (t, j) を witness にして、swap の 2 時刻 (t, t') と
   交換対象 job j' を取り出す。
   完全 Constructive: le_lt_dec / lt_dec のみ使用。Classical 不要。 *)
Lemma first_violation_has_repair_witness :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched (H : nat) t j,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    t < H ->
    sched t 0 = Some j ->
    edf_violation_at_with J candidates_of jobs sched t ->
    exists j' t',
      J j' /\
      eligible jobs 1 sched j' t /\
      job_abs_deadline (jobs j') < job_abs_deadline (jobs j) /\
      t <= t' /\
      t' < job_abs_deadline (jobs j') /\
      sched t' 0 = Some j'.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H t j
         _HJbool Hvalid Hfeas _HtH Hsched Hviol.
  (* Step 1: unfold violation to get running job j0 and earlier-deadline job j' *)
  unfold edf_violation_at_with, edf_violation_at_in in Hviol.
  destruct Hviol as [j0 [j' [_HJj0 [HJj' [Hsched0 [_Hin [Helig Hlt]]]]]]].
  (* Step 2: j0 = j from deterministic schedule *)
  rewrite Hsched in Hsched0.
  injection Hsched0 as Heq. subst j0.
  (* Step 3: j' is eligible and J j', so it runs before its deadline *)
  destruct (eligible_feasible_implies_runs_later_before_deadline
              J jobs sched j' t HJj' Hvalid Hfeas Helig)
      as [t' [Hle [Hlt' Hrun]]].
  (* Assemble witness (j', t') *)
  exists j', t'.
  split. exact HJj'.
  split. exact Helig.
  split. exact Hlt.
  split. exact Hle.
  split. exact Hlt'.
  exact Hrun.
Qed.

(* ===== Phase 3: repair schedule を定義する ===== *)

(* 5. swap_at:
   Single-CPU (CPU 0) 2-point swap.
   At t1: returns what was at t2; at t2: returns what was at t1.
   All other (t, c) are unchanged.
   Works correctly even when t1 = t2 (identity). *)
Definition swap_at
    (sched : Schedule)
    (t1 t2 : Time) : Schedule :=
  fun t c =>
    if Nat.eqb c 0 then
      if Nat.eqb t t1 then sched t2 0
      else if Nat.eqb t t2 then sched t1 0
      else sched t c
    else sched t c.

(* 6. swap_at_same_outside:
   If c ≠ 0 OR the time slot is neither t1 nor t2, swap_at is the identity.
   Constructive proof by Nat.eqb case analysis. *)
Lemma swap_at_same_outside :
  forall sched t1 t2 t c,
    c <> 0 \/ (t <> t1 /\ t <> t2) ->
    swap_at sched t1 t2 t c = sched t c.
Proof.
  intros sched t1 t2 t c Hor.
  unfold swap_at.
  destruct (Nat.eqb c 0) eqn:Hc.
  - apply Nat.eqb_eq in Hc. subst c.
    destruct Hor as [Hne | [Hne1 Hne2]].
    + exact (False_ind _ (Hne eq_refl)).
    + apply Nat.eqb_neq in Hne1. rewrite Hne1.
      apply Nat.eqb_neq in Hne2. rewrite Hne2.
      reflexivity.
  - reflexivity.
Qed.

(* 7a. swap_at_t1:
   At time t1 on CPU 0, swap_at gives what was at t2. *)
Lemma swap_at_t1 :
  forall sched t1 t2,
    swap_at sched t1 t2 t1 0 = sched t2 0.
Proof.
  intros sched t1 t2.
  unfold swap_at.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* 7b. swap_at_t2:
   At time t2 on CPU 0, swap_at gives what was at t1.
   When t2 = t1 the Nat.eqb t2 t1 branch fires instead, which is also correct
   because in that case sched t1 0 = sched t2 0. *)
Lemma swap_at_t2 :
  forall sched t1 t2,
    swap_at sched t1 t2 t2 0 = sched t1 0.
Proof.
  intros sched t1 t2.
  unfold swap_at.
  rewrite Nat.eqb_refl.
  destruct (Nat.eqb t2 t1) eqn:Ht.
  - apply Nat.eqb_eq in Ht. subst t1. reflexivity.
  - rewrite Nat.eqb_refl. reflexivity.
Qed.
