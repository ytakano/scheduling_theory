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

(* ===== Phase 4: swap が service に与える影響を解析する ===== *)

(* --- CPU-count helpers for m=1 under swap_at --- *)

(* At time t1, cpu_count in swap equals cpu_count in orig at t2. *)
Lemma cpu_count_1_swap_at_t1 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t1 = cpu_count 1 sched j t2.
Proof.
  intros sched t1 t2 j.
  simpl. unfold runs_on. rewrite swap_at_t1. reflexivity.
Qed.

(* At time t2, cpu_count in swap equals cpu_count in orig at t1. *)
Lemma cpu_count_1_swap_at_t2 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t2 = cpu_count 1 sched j t1.
Proof.
  intros sched t1 t2 j.
  simpl. unfold runs_on. rewrite swap_at_t2. reflexivity.
Qed.

(* At any time other than t1 or t2, cpu_count is unchanged. *)
Lemma cpu_count_1_swap_at_other :
  forall sched t1 t2 j t,
    t <> t1 -> t <> t2 ->
    cpu_count 1 (swap_at sched t1 t2) j t = cpu_count 1 sched j t.
Proof.
  intros sched t1 t2 j t Hne1 Hne2.
  simpl. unfold runs_on.
  rewrite (swap_at_same_outside sched t1 t2 t 0 (or_intror (conj Hne1 Hne2))).
  reflexivity.
Qed.

(* When sched t 0 = Some j, cpu_count 1 sched j t = 1. *)
Lemma cpu_count_1_some_eq :
  forall sched j t,
    sched t 0 = Some j ->
    cpu_count 1 sched j t = 1.
Proof.
  intros sched j t Hsome.
  assert (Hrun : runs_on sched j t 0 = true).
  { apply runs_on_true_iff. exact Hsome. }
  simpl. rewrite Hrun. simpl. reflexivity.
Qed.

(* When sched t 0 = Some j' with j <> j', cpu_count 1 sched j t = 0. *)
Lemma cpu_count_1_some_neq :
  forall sched j j' t,
    sched t 0 = Some j' ->
    j <> j' ->
    cpu_count 1 sched j t = 0.
Proof.
  intros sched j j' t Hsome Hne.
  apply (proj2 (cpu_count_zero_iff_not_executed 1 sched j t)).
  intros c Hlt Heq.
  assert (Hc : c = 0) by lia. subst c.
  rewrite Hsome in Heq.
  injection Heq as Heq'. subst j'.
  exact (Hne eq_refl).
Qed.

(* --- Pointwise cpu_count equality implies service_job equality --- *)

Lemma service_job_eq_of_cpu_count_eq :
  forall m (sched1 sched2 : Schedule) j T,
    (forall t, t < T -> cpu_count m sched1 j t = cpu_count m sched2 j t) ->
    service_job m sched1 j T = service_job m sched2 j T.
Proof.
  intros m sched1 sched2 j T Heq.
  induction T as [| T' IH].
  - simpl. reflexivity.
  - rewrite (service_job_step m sched1 j T').
    rewrite (service_job_step m sched2 j T').
    rewrite (Heq T' (Nat.lt_succ_diag_r T')).
    f_equal.
    apply IH.
    intros t Hlt. apply Heq. lia.
Qed.

(* 8. swap_at_service_unchanged_other_job:
   For j distinct from both swapped jobs, service_job is unaffected at all T.
   Constructive proof: case-split on t = t1 / t = t2 / neither. *)
Lemma swap_at_service_unchanged_other_job :
  forall sched j j1 j2 t1 t2 T,
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j <> j1 ->
    j <> j2 ->
    service_job 1 (swap_at sched t1 t2) j T =
    service_job 1 sched j T.
Proof.
  intros sched j j1 j2 t1 t2 T Hj1 Hj2 Hne1 Hne2.
  apply service_job_eq_of_cpu_count_eq.
  intros t _.
  destruct (Nat.eq_dec t t1) as [-> | Ht1ne].
  - (* t = t1: swap sees j2 there; orig sees j1 there; both ≠ j → both 0 *)
    rewrite cpu_count_1_swap_at_t1.
    rewrite (cpu_count_1_some_neq sched j j2 t2 Hj2 Hne2).
    rewrite (cpu_count_1_some_neq sched j j1 t1 Hj1 Hne1).
    reflexivity.
  - destruct (Nat.eq_dec t t2) as [-> | Ht2ne].
    + (* t = t2: swap sees j1 there; orig sees j2 there; both ≠ j → both 0 *)
      rewrite cpu_count_1_swap_at_t2.
      rewrite (cpu_count_1_some_neq sched j j1 t1 Hj1 Hne1).
      rewrite (cpu_count_1_some_neq sched j j2 t2 Hj2 Hne2).
      reflexivity.
    + (* t ≠ t1 and t ≠ t2: swap unchanged *)
      exact (cpu_count_1_swap_at_other sched t1 t2 j t Ht1ne Ht2ne).
Qed.

(* 9. swap_at_service_prefix_before_t1:
   For T ≤ t1 (and t1 ≤ t2), no swap point lies in [0,T), so service is unchanged.
   Constructive: every t < T satisfies t < t1 ≤ t2, so t ≠ t1 and t ≠ t2. *)
Lemma swap_at_service_prefix_before_t1 :
  forall sched j t1 t2 T,
    t1 <= t2 ->
    T <= t1 ->
    service_job 1 (swap_at sched t1 t2) j T =
    service_job 1 sched j T.
Proof.
  intros sched j t1 t2 T Hle12 HT.
  apply service_job_eq_of_cpu_count_eq.
  intros t Hlt.
  apply cpu_count_1_swap_at_other; lia.
Qed.

(* 10a. swap_at_service_j1_back_before_t2:
   j1 = sched t1 0 (back/delayed job). In the interval (t1, t2], j1 loses its
   t1 slot but does not yet gain the t2 slot, so orig service = 1 + swap service.
   Constructive induction on T with case T = S t1 (base) and T > S t1 (step). *)
Lemma swap_at_service_j1_back_before_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t1 < T ->
    T <= t2 ->
    service_job 1 sched j1 T = S (service_job 1 (swap_at sched t1 t2) j1 T).
Proof.
  intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne.
  induction T as [| T' IH]; intros Hgt1 Hle2.
  - lia.
  - rewrite (service_job_step 1 sched j1 T').
    rewrite (service_job_step 1 (swap_at sched t1 t2) j1 T').
    destruct (Nat.eq_dec T' t1) as [-> | HT'ne].
    + (* T' = t1, T = S t1: base case *)
      assert (Heq : service_job 1 (swap_at sched t1 t2) j1 t1 =
                    service_job 1 sched j1 t1).
      { apply (swap_at_service_prefix_before_t1 sched j1 t1 t2 t1);
          [lia | lia]. }
      rewrite Heq.
      assert (Hcpu_orig : cpu_count 1 sched j1 t1 = 1).
      { apply cpu_count_1_some_eq. exact Hj1. }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j1 t1 = 0).
      { rewrite cpu_count_1_swap_at_t1.
        apply (cpu_count_1_some_neq sched j1 j2 t2 Hj2 Hne). }
      lia.
    + (* T' ≠ t1, so T' > t1 (since T = S T' > t1 means T' >= t1) *)
      assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j1 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

(* 10b. swap_at_service_j2_front_before_t2:
   j2 = sched t2 0 (front/beneficiary job). In (t1, t2], j2 gains the t1 slot
   but does not yet lose the t2 slot, so swap service = 1 + orig service. *)
Lemma swap_at_service_j2_front_before_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t1 < T ->
    T <= t2 ->
    service_job 1 (swap_at sched t1 t2) j2 T = S (service_job 1 sched j2 T).
Proof.
  intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne.
  induction T as [| T' IH]; intros Hgt1 Hle2.
  - lia.
  - rewrite (service_job_step 1 (swap_at sched t1 t2) j2 T').
    rewrite (service_job_step 1 sched j2 T').
    destruct (Nat.eq_dec T' t1) as [-> | HT'ne].
    + (* T' = t1, T = S t1: base case *)
      assert (Heq : service_job 1 (swap_at sched t1 t2) j2 t1 =
                    service_job 1 sched j2 t1).
      { apply (swap_at_service_prefix_before_t1 sched j2 t1 t2 t1);
          [lia | lia]. }
      rewrite Heq.
      assert (Hcpu_orig : cpu_count 1 sched j2 t1 = 0).
      { apply (cpu_count_1_some_neq sched j2 j1 t1 Hj1).
        exact (fun H => Hne (eq_sym H)). }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t1 = 1).
      { rewrite cpu_count_1_swap_at_t1.
        apply cpu_count_1_some_eq. exact Hj2. }
      lia.
    + (* T' ≠ t1 so T' > t1 *)
      assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

(* 10c. swap_at_service_j1_after_t2:
   After t2, both the t1-loss and t2-gain of j1 are inside the window — net zero.
   Base case T = S t2: uses swap_at_service_j1_back_before_t2 at t2 to cancel.
   Inductive step T > S t2: cpu_count same at T' (≠ t1, ≠ t2). *)
Lemma swap_at_service_j1_after_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t2 < T ->
    service_job 1 (swap_at sched t1 t2) j1 T = service_job 1 sched j1 T.
Proof.
  intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne.
  induction T as [| T' IH]; intros Hlt.
  - lia.
  - rewrite (service_job_step 1 sched j1 T').
    rewrite (service_job_step 1 (swap_at sched t1 t2) j1 T').
    destruct (Nat.eq_dec T' t2) as [-> | HT'ne].
    + (* T' = t2, T = S t2: base case *)
      assert (Hcpu_orig : cpu_count 1 sched j1 t2 = 0).
      { apply (cpu_count_1_some_neq sched j1 j2 t2 Hj2 Hne). }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j1 t2 = 1).
      { rewrite cpu_count_1_swap_at_t2. apply cpu_count_1_some_eq. exact Hj1. }
      assert (Hservice : service_job 1 sched j1 t2 =
                         S (service_job 1 (swap_at sched t1 t2) j1 t2)).
      { apply (swap_at_service_j1_back_before_t2 sched j1 j2 t1 t2 t2
                 Hlt12 Hj1 Hj2 Hne); lia. }
      lia.
    + (* T' ≠ t2, T' > t2 *)
      assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j1 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

(* 10d. swap_at_service_j2_after_t2 (forward declaration for reference):
   Symmetric to 10c: after t2, j2's total service is unchanged. *)
Lemma swap_at_service_j2_after_t2 :
  forall sched j1 j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = Some j1 ->
    sched t2 0 = Some j2 ->
    j1 <> j2 ->
    t2 < T ->
    service_job 1 (swap_at sched t1 t2) j2 T = service_job 1 sched j2 T.
Proof.
  intros sched j1 j2 t1 t2 T Hlt12 Hj1 Hj2 Hne.
  induction T as [| T' IH]; intros Hlt.
  - lia.
  - rewrite (service_job_step 1 sched j2 T').
    rewrite (service_job_step 1 (swap_at sched t1 t2) j2 T').
    destruct (Nat.eq_dec T' t2) as [-> | HT'ne].
    + (* T' = t2, T = S t2: base case *)
      assert (Hcpu_orig : cpu_count 1 sched j2 t2 = 1).
      { apply cpu_count_1_some_eq. exact Hj2. }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t2 = 0).
      { rewrite cpu_count_1_swap_at_t2.
        apply (cpu_count_1_some_neq sched j2 j1 t1 Hj1).
        exact (fun H => Hne (eq_sym H)). }
      assert (Hservice : service_job 1 (swap_at sched t1 t2) j2 t2 =
                         S (service_job 1 sched j2 t2)).
      { apply (swap_at_service_j2_front_before_t2 sched j1 j2 t1 t2 t2
                 Hlt12 Hj1 Hj2 Hne); lia. }
      lia.
    + (* T' ≠ t2, T' > t2 *)
      assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

(* ===== Phase 5: swap が validity を壊さないことを示す ===== *)

(* Helper: In a valid single-CPU schedule, service_job never exceeds job_cost.
   Constructive induction: cpu_count = 0 → IH suffices; cpu_count = 1 → valid_schedule
   gives ~completed at that slot → service < job_cost → service + 1 ≤ job_cost. *)
Lemma valid_schedule_1_service_le_cost :
  forall jobs sched j T,
    valid_schedule jobs 1 sched ->
    service_job 1 sched j T <= job_cost (jobs j).
Proof.
  intros jobs sched j T Hvalid.
  induction T as [| T' IH].
  - simpl. lia.
  - rewrite service_job_step.
    destruct (Nat.eq_dec (cpu_count 1 sched j T') 0) as [Hz | Hnz].
    + rewrite Hz. lia.
    + assert (Hpos : 0 < cpu_count 1 sched j T') by lia.
      apply cpu_count_pos_iff_executed in Hpos.
      destruct Hpos as [c [Hlt Hrun]].
      assert (Hc : c = 0) by lia. subst c.
      assert (Hncomp : ~completed jobs 1 sched j T').
      { exact (valid_no_run_after_completion jobs 1 sched j T' 0 Hvalid
                 (Nat.lt_succ_diag_r 0) Hrun). }
      apply not_completed_iff_service_lt_cost in Hncomp.
      assert (Hcpu1 : cpu_count 1 sched j T' = 1).
      { apply cpu_count_1_some_eq. exact Hrun. }
      lia.
Qed.

(* 11. swap_at_validity_new_front_job:
   j' (the front/beneficiary job) placed at t in swap_at is eligible at t.
   Its release time is unchanged (released is schedule-independent).
   Its service up to t in swap equals service in orig by Lemma 9 (T ≤ t1 = t). *)
Lemma swap_at_validity_new_front_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    eligible jobs 1 sched j' t ->
    eligible jobs 1 (swap_at sched t t') j' t.
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Hle Helig.
  split.
  - exact (proj1 Helig).
  - intro Hcomp_swap.
    apply (proj2 Helig).
    unfold completed in *.
    rewrite (swap_at_service_prefix_before_t1 sched j' t t' t Hle (Nat.le_refl t))
      in Hcomp_swap.
    exact Hcomp_swap.
Qed.

(* 12. swap_at_validity_new_back_job:
   j (the back/delayed job) placed at t' in swap_at is eligible at t'.
   Released because j ran at t (valid_schedule → released at t) and t ≤ t'.
   Not completed: by Lemma 10a, service_swap(j, t') = service_orig(j, t') - 1,
   and service_orig(j, t') ≤ job_cost (valid_schedule_1_service_le_cost), so
   service_swap < job_cost. *)
Lemma swap_at_validity_new_back_job :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    eligible jobs 1 (swap_at sched t t') j t'.
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Hle Hdl.
  assert (Hne : j <> j') by (intro Heq; subst; lia).
  split.
  - (* released at t': j ran at t → released at t → monotone *)
    unfold released.
    apply (valid_no_run_before_release jobs 1 sched j t 0 Hvalid
             (Nat.lt_succ_diag_r 0)) in Hj.
    lia.
  - intro Hcomp_swap.
    unfold completed in Hcomp_swap.
    (* t = t' is impossible: both slots would equal Some j and Some j' → j = j' *)
    assert (Hlt : t < t').
    { destruct (Nat.eq_dec t t') as [Heqt | Hlt].
      - subst t'. rewrite Hj in Hj'. injection Hj' as Heqjj'. exfalso. exact (Hne Heqjj').
      - lia. }
    (* Lemma 10a: service_orig(j, t') = S(service_swap(j, t')) *)
    assert (Hservice : service_job 1 sched j t' =
                       S (service_job 1 (swap_at sched t t') j t')).
    { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t'
               Hlt Hj Hj' Hne Hlt (Nat.le_refl t')). }
    (* service_orig(j, t') ≤ job_cost *)
    assert (Hbound : service_job 1 sched j t' <= job_cost (jobs j)).
    { exact (valid_schedule_1_service_le_cost jobs sched j t' Hvalid). }
    lia.
Qed.

(* 13. swap_at_preserves_valid_schedule:
   Swapping j at t with j' at t' preserves the valid_schedule invariant.
   Case split on the running time t'':
   - t'' = t   → Lemma 11 (front job eligible)
   - t'' = t'  → Lemma 12 (back job eligible)
   - otherwise → orig eligibility, with service equality shown case-by-case:
       j'' ≠ j ∧ j'' ≠ j' : Lemma 8 (unchanged)
       j'' = j, t'' < t    : Lemma 9 (prefix)
       j'' = j, t < t'' < t': Lemma 10a (service decreases → stays < job_cost)
       j'' = j, t'' > t'   : Lemma 10c (unchanged after t')
       j'' = j', t'' < t   : Lemma 9 (prefix)
       j'' = j', t < t'' < t': key argument: service_orig(j',t'') + 1 ≤
                               service_orig(j',t') < job_cost (j' still runs at t')
       j'' = j', t'' > t'  : Lemma 10d (unchanged after t') *)
Lemma swap_at_preserves_valid_schedule :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
    valid_schedule jobs 1 (swap_at sched t t').
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Helig Hle Hdl.
  assert (Hne : j <> j') by (intro Heq; subst; lia).
  (* Derive t < t': if t = t', then j = j' (both run at t), contradiction *)
  assert (Hlt : t < t').
  { destruct (Nat.eq_dec t t') as [Heqt | Hlt].
    - subst t'. rewrite Hj in Hj'. injection Hj' as Heqjj'. exfalso. exact (Hne Heqjj').
    - lia. }
  unfold valid_schedule.
  intros j'' t'' c Hclt Hrun.
  assert (Hc : c = 0) by lia. subst c.
  destruct (Nat.eq_dec t'' t) as [-> | Htne].
  - (* t'' = t: running job is j' (from swap) *)
    rewrite swap_at_t1 in Hrun.
    rewrite Hj' in Hrun. injection Hrun as Heq. subst j''.
    exact (swap_at_validity_new_front_job
             jobs sched j j' t t' Hvalid Hj Hj' Hle Helig).
  - destruct (Nat.eq_dec t'' t') as [-> | Ht'ne].
    + (* t'' = t': running job is j (from swap) *)
      rewrite swap_at_t2 in Hrun.
      rewrite Hj in Hrun. injection Hrun as Heq. subst j''.
      exact (swap_at_validity_new_back_job
               jobs sched j j' t t' Hvalid Hj Hj' Hle Hdl).
    + (* t'' ≠ t, t'' ≠ t': swap is identity here *)
      rewrite (swap_at_same_outside sched t t' t'' 0
                 (or_intror (conj Htne Ht'ne))) in Hrun.
      assert (Helig_orig : eligible jobs 1 sched j'' t'').
      { exact (Hvalid j'' t'' 0 (Nat.lt_succ_diag_r 0) Hrun). }
      split.
      * exact (proj1 Helig_orig).
      * intro Hcomp_swap. unfold completed in *.
        destruct (Nat.eq_dec j'' j) as [-> | Hjne].
        { (* j'' = j *)
          destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
          - (* t'' < t: service unchanged (prefix) *)
            apply (proj2 Helig_orig).
            unfold completed.
            rewrite <- (swap_at_service_prefix_before_t1 sched j t t' t''
                          Hle (Nat.lt_le_incl t'' t Hlt_t)).
            exact Hcomp_swap.
          - assert (Hle_t : t <= t'') by lia.
            destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
            + (* t < t'' < t': Lemma 10a gives service_orig = S service_swap *)
              assert (Hlt12 : t < t') by lia.
              assert (Hlt_t : t < t'') by lia.
              assert (Hle_t' : t'' <= t') by lia.
              assert (Hservice : service_job 1 sched j t'' =
                                 S (service_job 1 (swap_at sched t t') j t'')).
              { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t''
                         Hlt12 Hj Hj' Hne Hlt_t Hle_t'). }
              apply (proj2 Helig_orig).
              unfold completed. lia.
            + (* t'' > t': Lemma 10c gives service_swap = service_orig *)
              assert (Hlt12 : t < t') by lia.
              assert (Hgt2 : t' < t'') by lia.
              apply (proj2 Helig_orig).
              unfold completed.
              rewrite <- (swap_at_service_j1_after_t2 sched j j' t t' t''
                            Hlt12 Hj Hj' Hne Hgt2).
              exact Hcomp_swap. }
        { destruct (Nat.eq_dec j'' j') as [-> | Hj'ne].
          { (* j'' = j' *)
            destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
            - (* t'' < t: service unchanged (prefix) *)
              apply (proj2 Helig_orig).
              unfold completed.
              rewrite <- (swap_at_service_prefix_before_t1 sched j' t t' t''
                            Hle (Nat.lt_le_incl t'' t Hlt_t)).
              exact Hcomp_swap.
            - assert (Hle_t : t <= t'') by lia.
              destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
              + (* t < t'' < t': key argument using both j' runs at t'' and at t' *)
                assert (Hlt12 : t < t') by exact Hlt.
                assert (Hlt_t'' : t < t'') by lia.
                assert (Hle_t'' : t'' <= t') by lia.
                assert (Hservice : service_job 1 (swap_at sched t t') j' t'' =
                                   S (service_job 1 sched j' t'')).
                { exact (swap_at_service_j2_front_before_t2 sched j j' t t' t''
                           Hlt12 Hj Hj' Hne Hlt_t'' Hle_t''). }
                (* service_orig(j', t''+1) = service_orig(j', t'') + 1 *)
                assert (Hcpu1 : cpu_count 1 sched j' t'' = 1).
                { apply cpu_count_1_some_eq. exact Hrun. }
                assert (Hstep : service_job 1 sched j' (S t'') =
                                S (service_job 1 sched j' t'')).
                { rewrite service_job_step. lia. }
                (* service_orig(j', t''+1) ≤ service_orig(j', t') *)
                assert (Hmono : service_job 1 sched j' (S t'') <=
                                service_job 1 sched j' t').
                { apply service_job_monotone. lia. }
                (* service_orig(j', t') < job_cost (j' runs at t' in valid sched) *)
                assert (Hncomp_t' : service_job 1 sched j' t' < job_cost (jobs j')).
                { apply not_completed_iff_service_lt_cost.
                  exact (valid_no_run_after_completion jobs 1 sched j' t' 0
                           Hvalid (Nat.lt_succ_diag_r 0) Hj'). }
                lia.
              + (* t'' > t': Lemma 10d gives service_swap = service_orig *)
                assert (Hlt12 : t < t') by lia.
                assert (Hgt2 : t' < t'') by lia.
                apply (proj2 Helig_orig).
                unfold completed.
                rewrite <- (swap_at_service_j2_after_t2 sched j j' t t' t''
                              Hlt12 Hj Hj' Hne Hgt2).
                exact Hcomp_swap. }
          { (* j'' ≠ j ∧ j'' ≠ j': Lemma 8 gives service unchanged *)
            apply (proj2 Helig_orig).
            unfold completed.
            rewrite <- (swap_at_service_unchanged_other_job sched j'' j j' t t' t''
                          Hj Hj' Hjne Hj'ne).
            exact Hcomp_swap. } }
Qed.
