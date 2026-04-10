From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import UniPolicies.EDF.
Require Import UniPolicies.EDFLemmas.
Require Import UniPolicies.EDFTransform.
Import ListNotations.

(* ===== Phase 9: EDF Optimality — exchange argument completes schedulability ===== *)

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

(* ===== cpu_count helper (needed by J_restrict_service_J) ===== *)

(* When sched t 0 = None, cpu_count 1 sched j t = 0 for any j. *)
Lemma cpu_count_1_none :
  forall sched j t,
    sched t 0 = None ->
    cpu_count 1 sched j t = 0.
Proof.
  intros sched j t Hnone.
  apply (proj2 (cpu_count_zero_iff_not_executed 1 sched j t)).
  intros c Hc.
  assert (Hc0 : c = 0) by lia. subst c.
  rewrite Hnone. discriminate.
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
    + (* J_bool j' = true → J_restrict keeps j' *)
      assert (HJR : J_restrict J_bool sched t 0 = Some j').
      { rewrite J_restrict_cpu0. rewrite Ht0. rewrite EJj'. reflexivity. }
      destruct (Nat.eq_dec j j') as [-> | Hne].
      * rewrite (cpu_count_1_some_eq (J_restrict J_bool sched) j' t HJR).
        symmetry. exact (cpu_count_1_some_eq sched j' t Ht0).
      * rewrite (cpu_count_1_some_neq (J_restrict J_bool sched) j j' t HJR Hne).
        symmetry. exact (cpu_count_1_some_neq sched j j' t Ht0 Hne).
    + (* J_bool j' = false → J_restrict gives None; j ≠ j' *)
      assert (HJR : J_restrict J_bool sched t 0 = None).
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

(* ===== Section 4: service lemmas for None-to-Some swap ===== *)

(* Analog of swap_at_service_j2_front_before_t2 for the None case.
   When sched t1 0 = None (idle at t1) and sched t2 0 = Some j2,
   swapping moves j2 from t2 to t1.  In (t1, t2], swap has one extra j2 run. *)
Lemma swap_at_service_j2_front_before_t2_none :
  forall sched j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = None ->
    sched t2 0 = Some j2 ->
    t1 < T ->
    T <= t2 ->
    service_job 1 (swap_at sched t1 t2) j2 T = S (service_job 1 sched j2 T).
Proof.
  intros sched j2 t1 t2 T Hlt12 Ht1_none Ht2_j2.
  induction T as [| T' IH]; intros Hgt1 Hle2.
  - lia.
  - rewrite (service_job_step 1 (swap_at sched t1 t2) j2 T').
    rewrite (service_job_step 1 sched j2 T').
    destruct (Nat.eq_dec T' t1) as [-> | HT'ne].
    + (* T' = t1, T = S t1: base case *)
      assert (Heq : service_job 1 (swap_at sched t1 t2) j2 t1 =
                    service_job 1 sched j2 t1).
      { apply (swap_at_service_prefix_before_t1 sched j2 t1 t2 t1); lia. }
      rewrite Heq.
      assert (Hcpu_orig : cpu_count 1 sched j2 t1 = 0).
      { exact (cpu_count_1_none sched j2 t1 Ht1_none). }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t1 = 1).
      { rewrite cpu_count_1_swap_at_t1. apply cpu_count_1_some_eq. exact Ht2_j2. }
      lia.
    + (* T' ≠ t1 so T' > t1 *)
      assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

(* After t2: j2's service in swap = j2's service in orig (net zero). *)
Lemma swap_at_service_j2_after_t2_none :
  forall sched j2 t1 t2 T,
    t1 < t2 ->
    sched t1 0 = None ->
    sched t2 0 = Some j2 ->
    t2 < T ->
    service_job 1 (swap_at sched t1 t2) j2 T = service_job 1 sched j2 T.
Proof.
  intros sched j2 t1 t2 T Hlt12 Ht1_none Ht2_j2.
  induction T as [| T' IH]; intros Hlt.
  - lia.
  - rewrite (service_job_step 1 sched j2 T').
    rewrite (service_job_step 1 (swap_at sched t1 t2) j2 T').
    destruct (Nat.eq_dec T' t2) as [-> | HT'ne].
    + (* T' = t2, T = S t2: base case *)
      assert (Hcpu_orig : cpu_count 1 sched j2 t2 = 1).
      { apply cpu_count_1_some_eq. exact Ht2_j2. }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t2 = 0).
      { rewrite cpu_count_1_swap_at_t2. exact (cpu_count_1_none sched j2 t1 Ht1_none). }
      assert (Hservice : service_job 1 (swap_at sched t1 t2) j2 t2 =
                         S (service_job 1 sched j2 t2)).
      { apply (swap_at_service_j2_front_before_t2_none sched j2 t1 t2 t2 Hlt12 Ht1_none Ht2_j2); lia. }
      lia.
    + (* T' ≠ t2, T' > t2 *)
      assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

(* For j ≠ j2, service is unchanged by the None-to-Some swap. *)
Lemma swap_at_service_other_none :
  forall sched j2 t1 t2 j T,
    sched t1 0 = None ->
    sched t2 0 = Some j2 ->
    j <> j2 ->
    service_job 1 (swap_at sched t1 t2) j T = service_job 1 sched j T.
Proof.
  intros sched j2 t1 t2 j T Ht1_none Ht2_j2 Hne.
  apply service_job_eq_of_cpu_count_eq.
  intros t _.
  destruct (Nat.eq_dec t t1) as [-> | Ht1ne].
  - rewrite cpu_count_1_swap_at_t1.
    rewrite (cpu_count_1_some_neq sched j j2 t2 Ht2_j2 Hne).
    symmetry. exact (cpu_count_1_none sched j t1 Ht1_none).
  - destruct (Nat.eq_dec t t2) as [-> | Ht2ne].
    + rewrite cpu_count_1_swap_at_t2.
      rewrite (cpu_count_1_none sched j t1 Ht1_none).
      symmetry. exact (cpu_count_1_some_neq sched j j2 t2 Ht2_j2 Hne).
    + exact (cpu_count_1_swap_at_other sched t1 t2 j t Ht1ne Ht2ne).
Qed.

(* ===== Section 5: validity for None-to-Some swap ===== *)

Lemma swap_at_preserves_valid_schedule_none :
  forall jobs sched j2 t1 t2,
    valid_schedule jobs 1 sched ->
    sched t1 0 = None ->
    sched t2 0 = Some j2 ->
    eligible jobs 1 sched j2 t1 ->
    t1 < t2 ->
    valid_schedule jobs 1 (swap_at sched t1 t2).
Proof.
  intros jobs sched j2 t1 t2 Hvalid Ht1_none Ht2_j2 Helig Hlt.
  unfold valid_schedule.
  intros j'' t'' c Hclt Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  destruct (Nat.eq_dec t'' t1) as [-> | Ht1ne].
  - (* t'' = t1: running job is j2 *)
    rewrite swap_at_t1 in Hrun. rewrite Ht2_j2 in Hrun.
    injection Hrun as Heq. subst j''.
    split.
    + exact (proj1 Helig).
    + intro Hcomp_swap.
      apply (proj2 Helig). unfold completed in *.
      rewrite <- (swap_at_service_prefix_before_t1 sched j2 t1 t2 t1
                    (Nat.lt_le_incl t1 t2 Hlt) (Nat.le_refl t1)).
      exact Hcomp_swap.
  - destruct (Nat.eq_dec t'' t2) as [-> | Ht2ne].
    + (* t'' = t2: swap puts None there *)
      rewrite swap_at_t2 in Hrun. rewrite Ht1_none in Hrun. discriminate.
    + (* t'' ≠ t1, t'' ≠ t2: swap is identity *)
      rewrite (swap_at_same_outside sched t1 t2 t'' 0
                 (or_intror (conj Ht1ne Ht2ne))) in Hrun.
      assert (Helig_orig : eligible jobs 1 sched j'' t'')
        by exact (Hvalid j'' t'' 0 (Nat.lt_succ_diag_r 0) Hrun).
      split.
      * exact (proj1 Helig_orig).
      * intro Hcomp_swap. apply (proj2 Helig_orig). unfold completed in *.
        destruct (Nat.eq_dec j'' j2) as [-> | Hj2ne].
        { (* j'' = j2 *)
          destruct (lt_dec t'' t1) as [Hlt_t1 | Hge_t1].
          - rewrite <- (swap_at_service_prefix_before_t1 sched j2 t1 t2 t''
                          (Nat.lt_le_incl t1 t2 Hlt) (Nat.lt_le_incl t'' t1 Hlt_t1)).
            exact Hcomp_swap.
          - destruct (lt_dec t'' t2) as [Hlt_t2 | Hge_t2].
            + (* t1 < t'' < t2 *)
              assert (Hlt12' : t1 < t'') by lia.
              assert (Hle_t2 : t'' <= t2) by lia.
              assert (Hservice_sw : service_job 1 (swap_at sched t1 t2) j2 t'' =
                                    S (service_job 1 sched j2 t'')).
              { exact (swap_at_service_j2_front_before_t2_none sched j2 t1 t2 t''
                           Hlt Ht1_none Ht2_j2 Hlt12' Hle_t2). }
              assert (Hcpu1 : cpu_count 1 sched j2 t'' = 1)
                by (apply cpu_count_1_some_eq; exact Hrun).
              assert (Hstep : service_job 1 sched j2 (S t'') = S (service_job 1 sched j2 t''))
                by (rewrite service_job_step; lia).
              assert (Hmono : service_job 1 sched j2 (S t'') <= service_job 1 sched j2 t2)
                by (apply service_job_monotone; lia).
              assert (Hncomp_t2 : service_job 1 sched j2 t2 < job_cost (jobs j2)).
              { apply not_completed_iff_service_lt_cost.
                exact (valid_no_run_after_completion jobs 1 sched j2 t2 0
                         Hvalid (Nat.lt_succ_diag_r 0) Ht2_j2). }
              lia.
            + assert (Hgt2 : t2 < t'') by lia.
              rewrite <- (swap_at_service_j2_after_t2_none sched j2 t1 t2 t''
                            Hlt Ht1_none Ht2_j2 Hgt2).
              exact Hcomp_swap. }
        { rewrite <- (swap_at_service_other_none sched j2 t1 t2 j'' t''
                        Ht1_none Ht2_j2 Hj2ne).
          exact Hcomp_swap. }
Qed.

(* ===== Section 6: feasibility for None-to-Some swap ===== *)

Lemma swap_at_preserves_feasible_schedule_on_none :
  forall J jobs sched j2 t1 t2,
    feasible_schedule_on J jobs 1 sched ->
    J j2 ->
    sched t1 0 = None ->
    sched t2 0 = Some j2 ->
    t1 < t2 ->
    t2 < job_abs_deadline (jobs j2) ->
    feasible_schedule_on J jobs 1 (swap_at sched t1 t2).
Proof.
  intros J jobs sched j2 t1 t2 Hfeas HJj2 Ht1_none Ht2_j2 Hlt Ht2_dl.
  unfold feasible_schedule_on.
  intros x HJx Hmiss.
  apply (Hfeas x HJx).
  unfold missed_deadline in *. unfold completed in *.
  destruct (Nat.eq_dec x j2) as [-> | Hxj2].
  - rewrite <- (swap_at_service_j2_after_t2_none sched j2 t1 t2
                  (job_abs_deadline (jobs j2)) Hlt Ht1_none Ht2_j2 Ht2_dl).
    exact Hmiss.
  - rewrite <- (swap_at_service_other_none sched j2 t1 t2 x
                  (job_abs_deadline (jobs x)) Ht1_none Ht2_j2 Hxj2).
    exact Hmiss.
Qed.

(* ===== Section 7: validity/feasibility for equal-deadline swap ===== *)

(* Analog of swap_at_validity_new_back_job but with j ≠ j' given directly. *)
Lemma swap_at_validity_new_back_job_ne :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    j <> j' ->
    t < t' ->
    eligible jobs 1 (swap_at sched t t') j t'.
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Hne Hlt.
  split.
  - unfold released.
    apply (valid_no_run_before_release jobs 1 sched j t 0 Hvalid
             (Nat.lt_succ_diag_r 0)) in Hj.
    lia.
  - intro Hcomp_swap. unfold completed in Hcomp_swap.
    assert (Hservice : service_job 1 sched j t' =
                       S (service_job 1 (swap_at sched t t') j t')).
    { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t'
               Hlt Hj Hj' Hne Hlt (Nat.le_refl t')). }
    assert (Hbound : service_job 1 sched j t' <= job_cost (jobs j))
      by exact (valid_schedule_1_service_le_cost jobs sched j t' Hvalid).
    lia.
Qed.

(* Validity for Some-Some swap with j ≠ j' given (not derived from deadline). *)
Lemma swap_at_preserves_valid_schedule_ne :
  forall jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    j <> j' ->
    valid_schedule jobs 1 (swap_at sched t t').
Proof.
  intros jobs sched j j' t t' Hvalid Hj Hj' Helig Hle Hne.
  assert (Hlt : t < t').
  { destruct (Nat.eq_dec t t') as [Heqt | Hne'].
    - subst t'. rewrite Hj in Hj'. injection Hj' as Heq. exfalso. exact (Hne Heq).
    - lia. }
  unfold valid_schedule.
  intros j'' t'' c Hclt Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  destruct (Nat.eq_dec t'' t) as [-> | Htne].
  - rewrite swap_at_t1 in Hrun. rewrite Hj' in Hrun.
    injection Hrun as Heq. subst j''.
    exact (swap_at_validity_new_front_job jobs sched j j' t t' Hvalid Hj Hj'
             (Nat.lt_le_incl t t' Hlt) Helig).
  - destruct (Nat.eq_dec t'' t') as [-> | Ht'ne].
    + rewrite swap_at_t2 in Hrun. rewrite Hj in Hrun.
      injection Hrun as Heq. subst j''.
      exact (swap_at_validity_new_back_job_ne jobs sched j j' t t' Hvalid Hj Hj' Hne Hlt).
    + rewrite (swap_at_same_outside sched t t' t'' 0
                 (or_intror (conj Htne Ht'ne))) in Hrun.
      assert (Helig_orig : eligible jobs 1 sched j'' t'')
        by exact (Hvalid j'' t'' 0 (Nat.lt_succ_diag_r 0) Hrun).
      split.
      * exact (proj1 Helig_orig).
      * intro Hcomp_swap. apply (proj2 Helig_orig). unfold completed in *.
        destruct (Nat.eq_dec j'' j) as [-> | Hjne].
        { destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
          - rewrite <- (swap_at_service_prefix_before_t1 sched j t t' t''
                          (Nat.lt_le_incl t t' Hlt) (Nat.lt_le_incl t'' t Hlt_t)).
            exact Hcomp_swap.
          - assert (Hle_t : t <= t'') by lia.
            destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
            + assert (Hlt12 : t < t') by lia.
              assert (Hlt_t'' : t < t'') by lia.
              assert (Hle_t'' : t'' <= t') by lia.
              assert (Hservice : service_job 1 sched j t'' =
                                 S (service_job 1 (swap_at sched t t') j t'')).
              { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t''
                          Hlt12 Hj Hj' Hne Hlt_t'' Hle_t''). }
              lia.
            + assert (Hgt2 : t' < t'') by lia.
              rewrite <- (swap_at_service_j1_after_t2 sched j j' t t' t''
                            Hlt Hj Hj' Hne Hgt2). exact Hcomp_swap. }
        { destruct (Nat.eq_dec j'' j') as [-> | Hj'ne].
          { destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
            - rewrite <- (swap_at_service_prefix_before_t1 sched j' t t' t''
                            (Nat.lt_le_incl t t' Hlt) (Nat.lt_le_incl t'' t Hlt_t)).
              exact Hcomp_swap.
            - assert (Hle_t : t <= t'') by lia.
              destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
              + assert (Hlt12 : t < t') by lia.
                assert (Hlt_t'' : t < t'') by lia.
                assert (Hle_t'' : t'' <= t') by lia.
                assert (Hservice_sw : service_job 1 (swap_at sched t t') j' t'' =
                                      S (service_job 1 sched j' t'')).
                { exact (swap_at_service_j2_front_before_t2 sched j j' t t' t''
                            Hlt12 Hj Hj' Hne Hlt_t'' Hle_t''). }
                assert (Hcpu1 : cpu_count 1 sched j' t'' = 1)
                  by (apply cpu_count_1_some_eq; exact Hrun).
                assert (Hstep : service_job 1 sched j' (S t'') = S (service_job 1 sched j' t''))
                  by (rewrite service_job_step; lia).
                assert (Hmono : service_job 1 sched j' (S t'') <= service_job 1 sched j' t')
                  by (apply service_job_monotone; lia).
                assert (Hncomp_t' : service_job 1 sched j' t' < job_cost (jobs j')).
                { apply not_completed_iff_service_lt_cost.
                  exact (valid_no_run_after_completion jobs 1 sched j' t' 0
                           Hvalid (Nat.lt_succ_diag_r 0) Hj'). }
                lia.
              + assert (Hgt2 : t' < t'') by lia.
                rewrite <- (swap_at_service_j2_after_t2 sched j j' t t' t''
                              Hlt Hj Hj' Hne Hgt2). exact Hcomp_swap. }
          { rewrite <- (swap_at_service_unchanged_other_job sched j'' j j' t t' t''
                          Hj Hj' Hjne Hj'ne). exact Hcomp_swap. } }
Qed.

(* Feasibility for Some-Some swap with deadline j' <= deadline j. *)
Lemma swap_at_preserves_feasible_schedule_on_le :
  forall J jobs sched j j' t t',
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    J j' ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    eligible jobs 1 sched j' t ->
    t <= t' ->
    t' < job_abs_deadline (jobs j') ->
    job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) ->
    feasible_schedule_on J jobs 1 (swap_at sched t t').
Proof.
  intros J jobs sched j j' t t' _Hvalid Hfeas HJj HJj' Hj Hj' _Helig Hle Hlt' Hdl.
  unfold feasible_schedule_on.
  intros x HJx.
  destruct (Nat.eq_dec x j') as [-> | Hxj'].
  - apply (swap_at_improves_front_job jobs sched j j' t t' Hle Hlt' Hj Hj').
    exact (Hfeas j' HJj').
  - destruct (Nat.eq_dec x j) as [-> | Hxj].
    + apply (swap_at_does_not_hurt_later_deadline_job jobs sched j j' t t' Hle).
      * lia.   (* t' < deadline(j') <= deadline(j) *)
      * exact Hj.
      * exact Hj'.
      * exact (Hfeas j HJj).
    + rewrite (swap_at_preserves_missed_deadline_other_job jobs sched j j' t t' x Hj Hj' Hxj Hxj').
      exact (Hfeas x HJx).
Qed.

(* ===== Section 8: Strong normalization ===== *)

(* Boolean: is the schedule canonical at time t? *)
Definition is_canonical_at_b
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : bool :=
  match sched t 0, choose_edf jobs 1 sched t (candidates_of jobs 1 sched t) with
  | None, None => true
  | Some j, Some j' => Nat.eqb j j'
  | _, _ => false
  end.

Lemma is_canonical_at_b_true_iff :
  forall candidates_of jobs sched t,
    is_canonical_at_b candidates_of jobs sched t = true <->
    matches_choose_edf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  unfold is_canonical_at_b, matches_choose_edf_at_with.
  destruct (sched t 0) as [j|] eqn:Es;
  destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Ec.
  - split.
    + intro H. apply Nat.eqb_eq in H. subst j'. reflexivity.
    + intro H. injection H as Heq. apply Nat.eqb_eq. exact Heq.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - split; intro H; reflexivity.
Qed.

Lemma is_canonical_at_b_false_iff :
  forall candidates_of jobs sched t,
    is_canonical_at_b candidates_of jobs sched t = false <->
    ~ matches_choose_edf_at_with jobs candidates_of sched t.
Proof.
  intros candidates_of jobs sched t.
  rewrite <- is_canonical_at_b_true_iff.
  destruct (is_canonical_at_b candidates_of jobs sched t).
  - split; intro H; [discriminate | exact (False_ind _ (H eq_refl))].
  - split; intro H; [intro Hf; discriminate | reflexivity].
Qed.

(* Repair lemma: if not canonical at t, produce a schedule that:
   - is still valid and feasible
   - agrees before t (so invariants from t' < t are preserved)
   - matches choose_edf at t
   Requires: J-only invariant (all running jobs are in J). *)
Lemma repair_non_canonical_at :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t' j, sched t' 0 = Some j -> J j) ->
    single_cpu_only sched ->
    ~ matches_choose_edf_at_with jobs candidates_of sched t ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t' j, sched' t' 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      agrees_before sched sched' t /\
      matches_choose_edf_at_with jobs candidates_of sched' t.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched t
         HJbool Hvalid Hfeas HJonly Hcpu1 Hnot.
  unfold matches_choose_edf_at_with in Hnot.
  (* Case split on sched t 0 *)
  destruct (sched t 0) as [j|] eqn:Hst0.
  - (* sched t 0 = Some j *)
    (* choose_edf must return Some j' with j' ≠ j *)
    destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + (* choose_edf = Some j'; j' ≠ j *)
      assert (Hne : j' <> j).
      { intro Heq. subst j'. apply Hnot. congruence. }
      assert (HJj : J j) by (exact (HJonly t j Hst0)).
      assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        exact (Hsound jobs 1 sched t j' (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose)). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by (exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose)).
      assert (Hdl_le : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
      { destruct cand_spec as [_ Hcomplete _].
        assert (Hin_j : In j (candidates_of jobs 1 sched t)).
        { apply Hcomplete. exact HJj. exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0). }
        exact (choose_edf_min_deadline jobs 1 sched t _ j' Hchoose j Hin_j
                 (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0)). }
      (* Find t' where j' runs in sched, t <= t' < deadline(j') *)
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      exists (swap_at sched t t').
      assert (Hlt : t < t' \/ t = t').
      { destruct (Nat.eq_dec t t') as [-> | Hne']. right. reflexivity. left. lia. }
      (* If t = t': sched t 0 = Some j but sched t' 0 = sched t 0 = Some j,
         j' must = j (since Ht'_run : sched t' 0 = Some j'), but j' ≠ j. Contradiction. *)
      assert (Hlt12 : t < t').
      { destruct Hlt as [H | Heq]. exact H.
        subst t'. rewrite Hst0 in Ht'_run. injection Ht'_run as Heqjj'.
        subst j. exfalso. exact (Hne eq_refl). }
      assert (Hagree : agrees_before sched (swap_at sched t t') t).
      { intros u c Hlu. symmetry.
        apply swap_at_same_outside. right. split; intro Heq; subst u; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact (swap_at_preserves_valid_schedule_ne jobs sched j j' t t'
                 Hvalid Hst0 Ht'_run Helig' (Nat.lt_le_incl t t' Hlt12)
                 (fun Heq => Hne (eq_sym Heq))).
      * exact (swap_at_preserves_feasible_schedule_on_le J jobs sched j j' t t'
                 Hvalid Hfeas HJj HJj' Hst0 Ht'_run Helig'
                 (Nat.lt_le_incl t t' Hlt12) Ht'_lt Hdl_le).
      * (* J-only preserved *)
        intros t'' j'' Hrun.
        destruct (Nat.eq_dec t'' t) as [-> | Ht''ne].
        -- rewrite swap_at_t1 in Hrun. rewrite Ht'_run in Hrun.
           injection Hrun as Heq. subst j''. exact HJj'.
        -- destruct (Nat.eq_dec t'' t') as [-> | Ht''ne'].
           ++ rewrite swap_at_t2 in Hrun. rewrite Hst0 in Hrun.
              injection Hrun as Heq. subst j''. exact HJj.
           ++ rewrite (swap_at_same_outside sched t t' t'' 0
                         (or_intror (conj Ht''ne Ht''ne'))) in Hrun.
              exact (HJonly t'' j'' Hrun).
      * exact (swap_at_single_cpu_only sched t t' Hcpu1).
      * exact Hagree.
      * unfold matches_choose_edf_at_with.
        rewrite swap_at_t1. rewrite Ht'_run.
        assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
          by (exact (agrees_before_sym _ _ _ Hagree)).
        rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
                   (swap_at sched t t') sched t Hagree_sym).
        rewrite (choose_edf_agrees_before jobs (swap_at sched t t') sched t _
                   Hagree_sym).
        exact (eq_sym Hchoose).
    + (* choose_edf = None: impossible since j is eligible and J j *)
      exfalso.
      assert (HJj : J j) by (exact (HJonly t j Hst0)).
      destruct cand_spec as [_ Hcomplete _].
      assert (Hin : In j (candidates_of jobs 1 sched t)).
      { apply Hcomplete. exact HJj. exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0). }
      assert (Helig : eligible jobs 1 sched j t)
        by exact (Hvalid j t 0 (Nat.lt_succ_diag_r 0) Hst0).
      destruct (choose_edf_some_if_exists jobs 1 sched t (candidates_of jobs 1 sched t)
                  (ex_intro _ j (conj Hin Helig))) as [j'' Hsome].
      rewrite Hchoose in Hsome. discriminate.
  - (* sched t 0 = None *)
    (* choose_edf must return Some j' (otherwise canonical) *)
    destruct (choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)) as [j'|] eqn:Hchoose.
    + (* choose_edf = Some j' *)
      assert (HJj' : J j').
      { destruct cand_spec as [Hsound _ _].
        exact (Hsound jobs 1 sched t j' (choose_edf_in_candidates jobs 1 sched t _ j' Hchoose)). }
      assert (Helig' : eligible jobs 1 sched j' t)
        by (exact (choose_edf_eligible jobs 1 sched t _ j' Hchoose)).
      destruct (eligible_feasible_implies_runs_later_before_deadline
                  J jobs sched j' t HJj' Hvalid Hfeas Helig')
          as [t' [Ht0_le [Ht'_lt Ht'_run]]].
      (* t ≤ t' and t ≠ t' since sched t 0 = None but sched t' 0 = Some j' *)
      assert (Hlt12 : t < t').
      { destruct (Nat.eq_dec t t') as [-> | Hne].
        - rewrite Hst0 in Ht'_run. discriminate.
        - lia. }
      exists (swap_at sched t t').
      assert (Hagree : agrees_before sched (swap_at sched t t') t).
      { intros u c Hlu. symmetry.
        apply swap_at_same_outside. right. split; intro Heq; subst u; lia. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      * exact (swap_at_preserves_valid_schedule_none jobs sched j' t t'
                 Hvalid Hst0 Ht'_run Helig' Hlt12).
      * exact (swap_at_preserves_feasible_schedule_on_none J jobs sched j' t t'
                 Hfeas HJj' Hst0 Ht'_run Hlt12 Ht'_lt).
      * intros t'' j'' Hrun.
        destruct (Nat.eq_dec t'' t) as [-> | Ht''ne].
        -- rewrite swap_at_t1 in Hrun. rewrite Ht'_run in Hrun.
           injection Hrun as Heq. subst j''. exact HJj'.
        -- destruct (Nat.eq_dec t'' t') as [-> | Ht''ne'].
           ++ rewrite swap_at_t2 in Hrun. rewrite Hst0 in Hrun. discriminate.
           ++ rewrite (swap_at_same_outside sched t t' t'' 0
                         (or_intror (conj Ht''ne Ht''ne'))) in Hrun.
              exact (HJonly t'' j'' Hrun).
      * exact (swap_at_single_cpu_only sched t t' Hcpu1).
      * exact Hagree.
      * unfold matches_choose_edf_at_with.
        rewrite swap_at_t1. rewrite Ht'_run.
        assert (Hagree_sym : agrees_before (swap_at sched t t') sched t)
          by (exact (agrees_before_sym _ _ _ Hagree)).
        rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
                   (swap_at sched t t') sched t Hagree_sym).
        rewrite (choose_edf_agrees_before jobs (swap_at sched t t') sched t _
                   Hagree_sym).
        exact (eq_sym Hchoose).
    + (* choose_edf = None and sched t 0 = None → canonical *)
      exfalso. apply Hnot.
      unfold matches_choose_edf_at_with. congruence.
Qed.

(* Propagation: repairing at t0 preserves canonical before t0. *)
Lemma repair_pushes_canonical_forward :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched sched' t0,
    single_cpu_only sched ->
    single_cpu_only sched' ->
    agrees_before sched sched' t0 ->
    matches_choose_edf_at_with jobs candidates_of sched' t0 ->
    matches_choose_edf_before jobs candidates_of sched t0 ->
    matches_choose_edf_before jobs candidates_of sched' (S t0).
Proof.
  intros J candidates_of cand_spec jobs sched sched' t0
         Honly Honly' Hagree Hmatch Hbefore.
  unfold matches_choose_edf_before.
  intros t Hlt.
  assert (Hcases : t < t0 \/ t = t0) by lia.
  destruct Hcases as [Hlt' | Heq].
  - (* t < t0: transfer from sched to sched' *)
    unfold matches_choose_edf_at_with.
    specialize (Hbefore t Hlt').
    unfold matches_choose_edf_at_with in Hbefore.
    (* sched and sched' agree before t0, so agree before t *)
    assert (Hpre : agrees_before sched sched' t).
    { apply (agrees_before_weaken sched sched' t t0). lia. exact Hagree. }
    assert (Hpre_sym : agrees_before sched' sched t)
      by (exact (agrees_before_sym _ _ _ Hpre)).
    (* sched' t 0 = sched t 0 (agree before t, and t < t0) *)
    assert (Hs't0 : sched' t 0 = sched t 0) by (symmetry; exact (Hagree t 0 Hlt')).
    (* candidates agree due to prefix extensionality *)
    assert (Hcand_eq : candidates_of jobs 1 sched' t = candidates_of jobs 1 sched t).
    { apply (candidates_prefix_extensional J candidates_of cand_spec jobs 1 sched' sched t).
      intros t' c Hlt''.
      destruct (Nat.eq_dec c 0) as [-> | Hcne].
      - symmetry. exact (Hpre t' 0 Hlt'').
      - assert (Hcpos : 0 < c) by lia.
        rewrite (Honly' t' c Hcpos). rewrite (Honly t' c Hcpos). reflexivity. }
    assert (Hchoose_eq : choose_edf jobs 1 sched' t (candidates_of jobs 1 sched' t) =
                         choose_edf jobs 1 sched t (candidates_of jobs 1 sched t)).
    { rewrite Hcand_eq.
      apply (choose_edf_agrees_before jobs sched' sched t (candidates_of jobs 1 sched t)).
      exact Hpre_sym. }
    rewrite Hs't0. rewrite Hchoose_eq. exact Hbefore.
  - subst t. exact Hmatch.
Qed.

(* Strong normalization: produce a schedule that exactly matches choose_edf before H. *)
Lemma edf_normalize_to_canonical :
  forall J (J_bool : JobId -> bool) (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    (forall x, J_bool x = true <-> J x) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    (forall t j, sched t 0 = Some j -> J j) ->
    single_cpu_only sched ->
    exists sched',
      valid_schedule jobs 1 sched' /\
      feasible_schedule_on J jobs 1 sched' /\
      (forall t j, sched' t 0 = Some j -> J j) /\
      single_cpu_only sched' /\
      matches_choose_edf_before jobs candidates_of sched' H.
Proof.
  intros J J_bool candidates_of cand_spec jobs sched H HJbool.
  induction H as [| H' IH].
  - intros Hvalid Hfeas HJonly Hcpu1.
    exists sched.
    refine (conj Hvalid (conj Hfeas (conj HJonly (conj Hcpu1 _)))).
    unfold matches_choose_edf_before. intros t Hlt. lia.
  - intros Hvalid Hfeas HJonly Hcpu1.
    destruct (IH Hvalid Hfeas HJonly Hcpu1)
        as [sched_ih [Hih_valid [Hih_feas [Hih_Jonly [Hih_cpu1 Hih_canon]]]]].
    (* Decide: is sched_ih canonical at H'? *)
    destruct (is_canonical_at_b candidates_of jobs sched_ih H') eqn:Hb.
    + (* Canonical at H': done *)
      exists sched_ih.
      refine (conj Hih_valid (conj Hih_feas (conj Hih_Jonly (conj Hih_cpu1 _)))).
      unfold matches_choose_edf_before.
      intros t Hlt.
      assert (Hcases : t < H' \/ t = H') by lia.
      destruct Hcases as [Hlt' | Heq].
      * exact (Hih_canon t Hlt').
      * subst t. apply (is_canonical_at_b_true_iff candidates_of jobs sched_ih H'). exact Hb.
    + (* Not canonical at H': repair *)
      assert (Hnot : ~ matches_choose_edf_at_with jobs candidates_of sched_ih H').
      { apply (is_canonical_at_b_false_iff candidates_of jobs sched_ih H'). exact Hb. }
      destruct (repair_non_canonical_at J J_bool candidates_of cand_spec
                   jobs sched_ih H'
                   HJbool Hih_valid Hih_feas Hih_Jonly Hih_cpu1 Hnot)
          as [sched_r [Hr_valid [Hr_feas [Hr_Jonly [Hr_cpu1 [Hr_agree Hr_match]]]]]].
      exists sched_r.
      refine (conj Hr_valid (conj Hr_feas (conj Hr_Jonly (conj Hr_cpu1 _)))).
      exact (repair_pushes_canonical_forward J candidates_of cand_spec
               jobs sched_ih sched_r H'
               Hih_cpu1 Hr_cpu1 Hr_agree Hr_match Hih_canon).
Qed.

(* ===== Section 9: Truncation ===== *)

Definition trunc_sched (sched : Schedule) (H : nat) : Schedule :=
  fun t c => if t <? H then sched t c else None.

Lemma trunc_sched_before : forall sched H t c,
    t < H -> trunc_sched sched H t c = sched t c.
Proof.
  intros sched H t c Hlt.
  unfold trunc_sched.
  assert (E : t <? H = true) by (apply Nat.ltb_lt; exact Hlt).
  rewrite E. reflexivity.
Qed.

Lemma trunc_sched_after : forall sched H t c,
    H <= t -> trunc_sched sched H t c = None.
Proof.
  intros sched H t c Hle.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Lemma trunc_sched_single_cpu_only : forall sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H).
Proof.
  intros sched H Honly t c Hc.
  unfold trunc_sched.
  destruct (t <? H) eqn:E.
  - exact (Honly t c Hc).
  - reflexivity.
Qed.

Lemma trunc_sched_valid : forall jobs sched H,
    valid_schedule jobs 1 sched ->
    valid_schedule jobs 1 (trunc_sched sched H).
Proof.
  intros jobs sched H Hvalid j t c Hc Hrun.
  assert (Hc0 : c = 0) by lia. subst c.
  destruct (lt_dec t H) as [Hlt | Hge].
  - rewrite (trunc_sched_before sched H t 0 Hlt) in Hrun.
    assert (Helig : eligible jobs 1 sched j t) by exact (Hvalid j t 0 Hc Hrun).
    split.
    + exact (proj1 Helig).
    + intro Hcomp. apply (proj2 Helig). unfold completed in *.
      (* service in trunc = service in orig for times < t *)
      assert (Heq : service_job 1 (trunc_sched sched H) j t =
                    service_job 1 sched j t).
      { apply service_job_eq_of_cpu_count_eq. intros t'' Hlt''.
        destruct (lt_dec t'' H) as [Hlt''' | Hge'''].
        - simpl. unfold runs_on. rewrite (trunc_sched_before sched H t'' 0 Hlt'''). reflexivity.
        - exfalso. lia. }
      rewrite Heq in Hcomp. exact Hcomp.
  - rewrite (trunc_sched_after sched H t 0 (proj1 (Nat.nlt_ge t H) Hge)) in Hrun.
    discriminate.
Qed.

Lemma trunc_sched_feasible : forall J jobs sched H,
    (forall j, J j -> job_abs_deadline (jobs j) <= H) ->
    feasible_schedule_on J jobs 1 sched ->
    feasible_schedule_on J jobs 1 (trunc_sched sched H).
Proof.
  intros J jobs sched H Hdl_le Hfeas j HJj Hmiss.
  apply (Hfeas j HJj).
  unfold missed_deadline in *. unfold completed in *.
  assert (Heq : service_job 1 (trunc_sched sched H) j (job_abs_deadline (jobs j)) =
                service_job 1 sched j (job_abs_deadline (jobs j))).
  { apply service_job_eq_of_cpu_count_eq. intros t Hlt.
    destruct (lt_dec t H) as [Hlt' | Hge'].
    - simpl. unfold runs_on. rewrite (trunc_sched_before sched H t 0 Hlt'). reflexivity.
    - assert (Hge : H <= t) by lia.
      assert (Hdl : job_abs_deadline (jobs j) <= H) by (exact (Hdl_le j HJj)).
      assert (HH : job_abs_deadline (jobs j) <= t) by lia.
      lia. }
  rewrite <- Heq. exact Hmiss.
Qed.

Lemma trunc_sched_canonical :
  forall J (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched H,
    single_cpu_only sched ->
    single_cpu_only (trunc_sched sched H) ->
    matches_choose_edf_before jobs candidates_of sched H ->
    matches_choose_edf_before jobs candidates_of (trunc_sched sched H) H.
Proof.
  intros J candidates_of cand_spec jobs sched H Honly Htrunc_only Hcanon.
  unfold matches_choose_edf_before, matches_choose_edf_at_with.
  intros t Hlt.
  rewrite (trunc_sched_before sched H t 0 Hlt).
  (* Need: choose_edf jobs 1 (trunc_sched sched H) t (candidates_of ...) =
           choose_edf jobs 1 sched t (candidates_of ...) *)
  assert (Hagree : agrees_before (trunc_sched sched H) sched t).
  { intros t' c Hlt''.
    rewrite (trunc_sched_before sched H t' c (Nat.lt_trans t' t H Hlt'' Hlt)).
    reflexivity. }
  assert (Hagree_sym : agrees_before sched (trunc_sched sched H) t)
    by (exact (agrees_before_sym _ _ _ Hagree)).
  rewrite (candidates_of_agrees_before J candidates_of cand_spec jobs
             (trunc_sched sched H) sched t Hagree).
  rewrite (choose_edf_agrees_before jobs (trunc_sched sched H) sched t _
             Hagree).
  exact (Hcanon t Hlt).
Qed.

(* ===== Section 10: Bridge to scheduler_rel ===== *)

(* All J jobs are completed at any time >= deadline_horizon. *)
Lemma J_jobs_complete_at_or_after_deadline :
  forall J jobs sched j t,
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    job_abs_deadline (jobs j) <= t ->
    completed jobs 1 sched j t.
Proof.
  intros J jobs sched j t _Hvalid Hfeas HJj Hdt.
  unfold completed.
  assert (Hnmiss : ~ missed_deadline jobs 1 sched j) by exact (Hfeas j HJj).
  unfold missed_deadline in Hnmiss. unfold completed in Hnmiss.
  assert (Hmono : service_job 1 sched j (job_abs_deadline (jobs j)) <=
                  service_job 1 sched j t)
    by (apply service_job_monotone; exact Hdt).
  lia.
Qed.

(* Hmm, let me check what lemmas are available. *)

Lemma J_jobs_not_eligible_at_horizon :
  forall J enumJ jobs sched j t,
    (forall x, J x -> In x enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    J j ->
    deadline_horizon jobs enumJ <= t ->
    ~eligible jobs 1 sched j t.
Proof.
  intros J enumJ jobs sched j t HJ_in Hvalid Hfeas HJj Hdt Helig.
  (* j's deadline < H <= t, so j should be completed by t *)
  assert (Hdl : job_abs_deadline (jobs j) < deadline_horizon jobs enumJ).
  { exact (J_implies_deadline_lt_horizon J enumJ jobs j HJ_in HJj). }
  assert (Hcomp : completed jobs 1 sched j t).
  { apply (J_jobs_complete_at_or_after_deadline J jobs sched j t Hvalid Hfeas HJj). lia. }
  exact (proj2 Helig Hcomp).
Qed.

(* Given matches_choose_edf_before H and idle after H, build scheduler_rel. *)
Lemma canonical_and_idle_implies_scheduler_rel :
  forall J enumJ (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched,
    (forall j, J j -> In j enumJ) ->
    valid_schedule jobs 1 sched ->
    feasible_schedule_on J jobs 1 sched ->
    single_cpu_only sched ->
    matches_choose_edf_before jobs candidates_of sched (deadline_horizon jobs enumJ) ->
    (forall t, deadline_horizon jobs enumJ <= t -> sched t 0 = None) ->
    scheduler_rel (edf_scheduler candidates_of) jobs 1 sched.
Proof.
  intros J enumJ candidates_of cand_spec jobs sched
         HJ_in Hvalid Hfeas Honly Hcanon Hidle.
  unfold edf_scheduler, single_cpu_dispatch_scheduler_on, single_cpu_dispatch_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + (* sched t 0 = choose_edf jobs 1 sched t ... *)
      destruct (lt_dec t (deadline_horizon jobs enumJ)) as [Hlt | Hge].
      * (* t < H: from canonical *)
        exact (Hcanon t Hlt).
      * (* t >= H: both None *)
        assert (Ht_H : deadline_horizon jobs enumJ <= t) by lia.
        rewrite (Hidle t Ht_H).
        (* choose_edf = None since no J job is eligible *)
        symmetry.
        apply choose_edf_none_if_no_eligible.
        intros j Hin Helig.
        destruct cand_spec as [Hsound _ _].
        assert (HJj : J j) by (exact (Hsound jobs 1 sched t j Hin)).
        exact (J_jobs_not_eligible_at_horizon J enumJ jobs sched j t
                 HJ_in Hvalid Hfeas HJj Ht_H Helig).
    + exact (Honly t).
Qed.

(* ===== Section 11: Main theorem ===== *)

Theorem edf_optimality_on_finite_jobs :
  forall J (J_bool : JobId -> bool) enumJ
         (candidates_of : CandidateSource)
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs,
    (forall x, J_bool x = true <-> J x) ->
    (forall j, J j -> In j enumJ) ->
    (forall j, In j enumJ -> J j) ->
    feasible_on J jobs 1 ->
    schedulable_by_on J (edf_scheduler candidates_of) jobs 1.
Proof.
  intros J J_bool enumJ candidates_of cand_spec jobs
         HJbool HJ_in HJ_complete Hfeas_on.
  (* Step 1: extract feasible witness *)
  destruct Hfeas_on as [sched0 [Hvalid0 Hfeas0]].
  (* Step 2: restrict to CPU 0 only + J-only *)
  set (sched1 := J_restrict J_bool (mk_single_cpu sched0)).
  assert (Hvalid1 : valid_schedule jobs 1 sched1).
  { unfold sched1.
    apply (J_restrict_valid J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_valid jobs sched0 Hvalid0). }
  assert (Hfeas1 : feasible_schedule_on J jobs 1 sched1).
  { unfold sched1.
    apply (J_restrict_feasible J_bool J jobs (mk_single_cpu sched0) HJbool).
    exact (mk_single_cpu_feasible J jobs sched0 Hfeas0). }
  assert (HJonly1 : forall t j, sched1 t 0 = Some j -> J j).
  { intros t j Hrun. unfold sched1 in Hrun.
    exact (J_restrict_J_only J_bool J (mk_single_cpu sched0) t j HJbool Hrun). }
  assert (Hcpu1 : single_cpu_only sched1).
  { unfold sched1. exact (J_restrict_only J_bool (mk_single_cpu sched0)). }
  (* Step 3: strong normalization *)
  set (H := deadline_horizon jobs enumJ).
  destruct (edf_normalize_to_canonical J J_bool candidates_of cand_spec jobs sched1 H
               HJbool Hvalid1 Hfeas1 HJonly1 Hcpu1)
      as [sched2 [Hvalid2 [Hfeas2 [HJonly2 [Hcpu2 Hcanon2]]]]].
  (* Step 4: truncate *)
  set (sched3 := trunc_sched sched2 H).
  assert (Hvalid3 : valid_schedule jobs 1 sched3)
    by (unfold sched3; exact (trunc_sched_valid jobs sched2 H Hvalid2)).
  assert (Hfeas3 : feasible_schedule_on J jobs 1 sched3).
  { unfold sched3.
    apply (trunc_sched_feasible J jobs sched2 H).
    - intros j HJj. apply Nat.lt_le_incl.
      unfold H. exact (J_implies_deadline_lt_horizon J enumJ jobs j HJ_in HJj).
    - exact Hfeas2. }
  assert (Hcpu3 : single_cpu_only sched3).
  { unfold sched3. exact (trunc_sched_single_cpu_only sched2 H Hcpu2). }
  assert (Hcanon3 : matches_choose_edf_before jobs candidates_of sched3 H).
  { unfold sched3.
    exact (trunc_sched_canonical J candidates_of cand_spec jobs sched2 H
             Hcpu2 (trunc_sched_single_cpu_only sched2 H Hcpu2) Hcanon2). }
  assert (Hidle3 : forall t, H <= t -> sched3 t 0 = None).
  { intros t Hle. unfold sched3.
    exact (trunc_sched_after sched2 H t 0 Hle). }
  (* Step 5: apply bridge *)
  assert (Hrel : scheduler_rel (edf_scheduler candidates_of) jobs 1 sched3).
  { exact (canonical_and_idle_implies_scheduler_rel J enumJ candidates_of cand_spec
             jobs sched3 HJ_in Hvalid3 Hfeas3 Hcpu3 Hcanon3 Hidle3). }
  (* Step 6: apply schedulable_by_on intro *)
  exact (single_cpu_dispatch_schedulable_by_on_intro J edf_generic_spec candidates_of
           cand_spec jobs sched3 Hrel Hfeas3).
Qed.
