From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Import ListNotations.

(* ===== Section 1: swap_at definition and basic lemmas ===== *)

Definition swap_at
    (sched : Schedule)
    (t1 t2 : Time) : Schedule :=
  fun t c =>
    if Nat.eqb c 0 then
      if Nat.eqb t t1 then sched t2 0
      else if Nat.eqb t t2 then sched t1 0
      else sched t c
    else sched t c.

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

(* ===== Section 2: CPU-count helpers for m=1 under swap_at ===== *)

Lemma cpu_count_1_swap_at_t1 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t1 = cpu_count 1 sched j t2.
Proof.
  intros sched t1 t2 j.
  simpl. unfold runs_on. rewrite swap_at_t1. reflexivity.
Qed.

Lemma cpu_count_1_swap_at_t2 :
  forall sched t1 t2 j,
    cpu_count 1 (swap_at sched t1 t2) j t2 = cpu_count 1 sched j t1.
Proof.
  intros sched t1 t2 j.
  simpl. unfold runs_on. rewrite swap_at_t2. reflexivity.
Qed.

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

(* ===== Section 3: Pointwise cpu_count equality implies service_job equality ===== *)

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

(* ===== Section 4: Swap service lemmas (Some-Some case) ===== *)

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
  - rewrite cpu_count_1_swap_at_t1.
    rewrite (cpu_count_1_some_neq sched j j2 t2 Hj2 Hne2).
    rewrite (cpu_count_1_some_neq sched j j1 t1 Hj1 Hne1).
    reflexivity.
  - destruct (Nat.eq_dec t t2) as [-> | Ht2ne].
    + rewrite cpu_count_1_swap_at_t2.
      rewrite (cpu_count_1_some_neq sched j j1 t1 Hj1 Hne1).
      rewrite (cpu_count_1_some_neq sched j j2 t2 Hj2 Hne2).
      reflexivity.
    + exact (cpu_count_1_swap_at_other sched t1 t2 j t Ht1ne Ht2ne).
Qed.

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
    + assert (Heq : service_job 1 (swap_at sched t1 t2) j1 t1 =
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
    + assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j1 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

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
    + assert (Heq : service_job 1 (swap_at sched t1 t2) j2 t1 =
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
    + assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

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
    + assert (Hcpu_orig : cpu_count 1 sched j1 t2 = 0).
      { apply (cpu_count_1_some_neq sched j1 j2 t2 Hj2 Hne). }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j1 t2 = 1).
      { rewrite cpu_count_1_swap_at_t2. apply cpu_count_1_some_eq. exact Hj1. }
      assert (Hservice : service_job 1 sched j1 t2 =
                         S (service_job 1 (swap_at sched t1 t2) j1 t2)).
      { apply (swap_at_service_j1_back_before_t2 sched j1 j2 t1 t2 t2
                 Hlt12 Hj1 Hj2 Hne); lia. }
      lia.
    + assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j1 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

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
    + assert (Hcpu_orig : cpu_count 1 sched j2 t2 = 1).
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
    + assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

(* ===== Section 5: Validity helpers for swap_at (Some-Some) ===== *)

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
  - unfold released.
    apply (valid_no_run_before_release jobs 1 sched j t 0 Hvalid
             (Nat.lt_succ_diag_r 0)) in Hj.
    lia.
  - intro Hcomp_swap.
    unfold completed in Hcomp_swap.
    assert (Hlt : t < t').
    { destruct (Nat.eq_dec t t') as [Heqt | Hlt].
      - subst t'. rewrite Hj in Hj'. injection Hj' as Heqjj'. exfalso. exact (Hne Heqjj').
      - lia. }
    assert (Hservice : service_job 1 sched j t' =
                       S (service_job 1 (swap_at sched t t') j t')).
    { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t'
               Hlt Hj Hj' Hne Hlt (Nat.le_refl t')). }
    assert (Hbound : service_job 1 sched j t' <= job_cost (jobs j)).
    { exact (valid_schedule_1_service_le_cost jobs sched j t' Hvalid). }
    lia.
Qed.

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
  assert (Hlt : t < t').
  { destruct (Nat.eq_dec t t') as [Heqt | Hlt].
    - subst t'. rewrite Hj in Hj'. injection Hj' as Heqjj'. exfalso. exact (Hne Heqjj').
    - lia. }
  unfold valid_schedule.
  intros j'' t'' c Hclt Hrun.
  assert (Hc : c = 0) by lia. subst c.
  destruct (Nat.eq_dec t'' t) as [-> | Htne].
  - rewrite swap_at_t1 in Hrun.
    rewrite Hj' in Hrun. injection Hrun as Heq. subst j''.
    exact (swap_at_validity_new_front_job
             jobs sched j j' t t' Hvalid Hj Hj' Hle Helig).
  - destruct (Nat.eq_dec t'' t') as [-> | Ht'ne].
    + rewrite swap_at_t2 in Hrun.
      rewrite Hj in Hrun. injection Hrun as Heq. subst j''.
      exact (swap_at_validity_new_back_job
               jobs sched j j' t t' Hvalid Hj Hj' Hle Hdl).
    + rewrite (swap_at_same_outside sched t t' t'' 0
                 (or_intror (conj Htne Ht'ne))) in Hrun.
      assert (Helig_orig : eligible jobs 1 sched j'' t'').
      { exact (Hvalid j'' t'' 0 (Nat.lt_succ_diag_r 0) Hrun). }
      split.
      * exact (proj1 Helig_orig).
      * intro Hcomp_swap. unfold completed in *.
        destruct (Nat.eq_dec j'' j) as [-> | Hjne].
        { destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
          - apply (proj2 Helig_orig).
            unfold completed.
            rewrite <- (swap_at_service_prefix_before_t1 sched j t t' t''
                          Hle (Nat.lt_le_incl t'' t Hlt_t)).
            exact Hcomp_swap.
          - assert (Hle_t : t <= t'') by lia.
            destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
            + assert (Hlt12 : t < t') by lia.
              assert (Hlt_t : t < t'') by lia.
              assert (Hle_t' : t'' <= t') by lia.
              assert (Hservice : service_job 1 sched j t'' =
                                 S (service_job 1 (swap_at sched t t') j t'')).
              { exact (swap_at_service_j1_back_before_t2 sched j j' t t' t''
                         Hlt12 Hj Hj' Hne Hlt_t Hle_t'). }
              apply (proj2 Helig_orig).
              unfold completed. lia.
            + assert (Hlt12 : t < t') by lia.
              assert (Hgt2 : t' < t'') by lia.
              apply (proj2 Helig_orig).
              unfold completed.
              rewrite <- (swap_at_service_j1_after_t2 sched j j' t t' t''
                            Hlt12 Hj Hj' Hne Hgt2).
              exact Hcomp_swap. }
        { destruct (Nat.eq_dec j'' j') as [-> | Hj'ne].
          { destruct (lt_dec t'' t) as [Hlt_t | Hge_t].
            - apply (proj2 Helig_orig).
              unfold completed.
              rewrite <- (swap_at_service_prefix_before_t1 sched j' t t' t''
                            Hle (Nat.lt_le_incl t'' t Hlt_t)).
              exact Hcomp_swap.
            - assert (Hle_t : t <= t'') by lia.
              destruct (lt_dec t'' t') as [Hlt_t' | Hge_t'].
              + assert (Hlt12 : t < t') by exact Hlt.
                assert (Hlt_t'' : t < t'') by lia.
                assert (Hle_t'' : t'' <= t') by lia.
                assert (Hservice : service_job 1 (swap_at sched t t') j' t'' =
                                   S (service_job 1 sched j' t'')).
                { exact (swap_at_service_j2_front_before_t2 sched j j' t t' t''
                           Hlt12 Hj Hj' Hne Hlt_t'' Hle_t''). }
                assert (Hcpu1 : cpu_count 1 sched j' t'' = 1).
                { apply cpu_count_1_some_eq. exact Hrun. }
                assert (Hstep : service_job 1 sched j' (S t'') =
                                S (service_job 1 sched j' t'')).
                { rewrite service_job_step. lia. }
                assert (Hmono : service_job 1 sched j' (S t'') <=
                                service_job 1 sched j' t').
                { apply service_job_monotone. lia. }
                assert (Hncomp_t' : service_job 1 sched j' t' < job_cost (jobs j')).
                { apply not_completed_iff_service_lt_cost.
                  exact (valid_no_run_after_completion jobs 1 sched j' t' 0
                           Hvalid (Nat.lt_succ_diag_r 0) Hj'). }
                lia.
              + assert (Hlt12 : t < t') by lia.
                assert (Hgt2 : t' < t'') by lia.
                apply (proj2 Helig_orig).
                unfold completed.
                rewrite <- (swap_at_service_j2_after_t2 sched j j' t t' t''
                              Hlt12 Hj Hj' Hne Hgt2).
                exact Hcomp_swap. }
          { apply (proj2 Helig_orig).
            unfold completed.
            rewrite <- (swap_at_service_unchanged_other_job sched j'' j j' t t' t''
                          Hj Hj' Hjne Hj'ne).
            exact Hcomp_swap. } }
Qed.

(* ===== Section 6: Missed-deadline and feasibility (Some-Some, strict deadline) ===== *)

Lemma swap_at_preserves_missed_deadline_other_job :
  forall jobs sched j j' t t' x,
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    x <> j ->
    x <> j' ->
    missed_deadline jobs 1 (swap_at sched t t') x <->
    missed_deadline jobs 1 sched x.
Proof.
  intros jobs sched j j' t t' x Hj Hj' Hxj Hxj'.
  rewrite !missed_deadline_iff_service_lt_cost_at_deadline.
  rewrite (swap_at_service_unchanged_other_job sched x j j' t t'
             (job_abs_deadline (jobs x)) Hj Hj' Hxj Hxj').
  tauto.
Qed.

Lemma swap_at_improves_front_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j') ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    ~ missed_deadline jobs 1 sched j' ->
    ~ missed_deadline jobs 1 (swap_at sched t t') j'.
Proof.
  intros jobs sched j j' t t' Hle Hlt' Hj Hj' Hnmiss.
  rewrite missed_deadline_iff_service_lt_cost_at_deadline in *.
  destruct (Nat.eq_dec j j') as [-> | Hne].
  - rewrite (service_job_eq_of_cpu_count_eq 1 (swap_at sched t t') sched j'
               (job_abs_deadline (jobs j'))).
    + exact Hnmiss.
    + intros t'' _.
      destruct (Nat.eq_dec t'' t) as [-> | Ht1ne].
      * rewrite cpu_count_1_swap_at_t1.
        rewrite (cpu_count_1_some_eq sched j' t' Hj').
        rewrite (cpu_count_1_some_eq sched j' t Hj).
        reflexivity.
      * destruct (Nat.eq_dec t'' t') as [-> | Ht2ne].
        -- rewrite cpu_count_1_swap_at_t2.
           rewrite (cpu_count_1_some_eq sched j' t Hj).
           rewrite (cpu_count_1_some_eq sched j' t' Hj').
           reflexivity.
        -- rewrite (cpu_count_1_swap_at_other sched t t' j' t'' Ht1ne Ht2ne).
           reflexivity.
  - assert (Hlt : t < t').
    { destruct (Nat.eq_dec t t') as [Heqt | H].
      - subst t'. rewrite Hj in Hj'. injection Hj' as Heq. exfalso. exact (Hne Heq).
      - lia. }
    rewrite (swap_at_service_j2_after_t2 sched j j' t t'
               (job_abs_deadline (jobs j')) Hlt Hj Hj' Hne Hlt').
    exact Hnmiss.
Qed.

Lemma swap_at_service_at_deadline_same_for_back_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j) ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    service_job 1 (swap_at sched t t') j (job_abs_deadline (jobs j)) =
    service_job 1 sched j (job_abs_deadline (jobs j)).
Proof.
  intros jobs sched j j' t t' Hle Hlt Hj Hj'.
  destruct (Nat.eq_dec j j') as [-> | Hne].
  - apply service_job_eq_of_cpu_count_eq.
    intros t'' _.
    destruct (Nat.eq_dec t'' t) as [-> | Ht1ne].
    + rewrite cpu_count_1_swap_at_t1.
      rewrite (cpu_count_1_some_eq sched j' t' Hj').
      rewrite (cpu_count_1_some_eq sched j' t Hj).
      reflexivity.
    + destruct (Nat.eq_dec t'' t') as [-> | Ht2ne].
      * rewrite cpu_count_1_swap_at_t2.
        rewrite (cpu_count_1_some_eq sched j' t Hj).
        rewrite (cpu_count_1_some_eq sched j' t' Hj').
        reflexivity.
      * rewrite (cpu_count_1_swap_at_other sched t t' j' t'' Ht1ne Ht2ne).
        reflexivity.
  - assert (Hlt12 : t < t').
    { destruct (Nat.eq_dec t t') as [Heqt | H].
      - subst. rewrite Hj in Hj'. injection Hj' as Heq. exfalso. exact (Hne Heq).
      - lia. }
    exact (swap_at_service_j1_after_t2 sched j j' t t'
             (job_abs_deadline (jobs j)) Hlt12 Hj Hj' Hne Hlt).
Qed.

Lemma swap_at_does_not_hurt_later_deadline_job :
  forall jobs sched j j' t t',
    t <= t' ->
    t' < job_abs_deadline (jobs j) ->
    sched t 0 = Some j ->
    sched t' 0 = Some j' ->
    ~ missed_deadline jobs 1 sched j ->
    ~ missed_deadline jobs 1 (swap_at sched t t') j.
Proof.
  intros jobs sched j j' t t' Hle Hlt' Hj Hj' Hnmiss.
  rewrite missed_deadline_iff_service_lt_cost_at_deadline in *.
  rewrite (swap_at_service_at_deadline_same_for_back_job jobs sched j j' t t' Hle Hlt' Hj Hj').
  exact Hnmiss.
Qed.

Lemma swap_at_preserves_feasible_schedule_on :
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
    job_abs_deadline (jobs j') < job_abs_deadline (jobs j) ->
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
      * lia.
      * exact Hj.
      * exact Hj'.
      * exact (Hfeas j HJj).
    + rewrite (swap_at_preserves_missed_deadline_other_job jobs sched j j' t t' x Hj Hj' Hxj Hxj').
      exact (Hfeas x HJx).
Qed.

(* ===== Section 7: Swap service lemmas (None-to-Some case) ===== *)

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
    + assert (Heq : service_job 1 (swap_at sched t1 t2) j2 t1 =
                    service_job 1 sched j2 t1).
      { apply (swap_at_service_prefix_before_t1 sched j2 t1 t2 t1); lia. }
      rewrite Heq.
      assert (Hcpu_orig : cpu_count 1 sched j2 t1 = 0).
      { exact (cpu_count_1_none sched j2 t1 Ht1_none). }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t1 = 1).
      { rewrite cpu_count_1_swap_at_t1. apply cpu_count_1_some_eq. exact Ht2_j2. }
      lia.
    + assert (HT'gt : t1 < T') by lia.
      assert (HT'ne_t2 : T' <> t2) by lia.
      assert (HT'le2 : T' <= t2) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne HT'ne_t2).
      rewrite (IH HT'gt HT'le2).
      lia.
Qed.

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
    + assert (Hcpu_orig : cpu_count 1 sched j2 t2 = 1).
      { apply cpu_count_1_some_eq. exact Ht2_j2. }
      assert (Hcpu_swap : cpu_count 1 (swap_at sched t1 t2) j2 t2 = 0).
      { rewrite cpu_count_1_swap_at_t2. exact (cpu_count_1_none sched j2 t1 Ht1_none). }
      assert (Hservice : service_job 1 (swap_at sched t1 t2) j2 t2 =
                         S (service_job 1 sched j2 t2)).
      { apply (swap_at_service_j2_front_before_t2_none sched j2 t1 t2 t2
                 Hlt12 Ht1_none Ht2_j2); lia. }
      lia.
    + assert (HT'gt : t2 < T') by lia.
      assert (HT'ne1 : T' <> t1) by lia.
      rewrite (cpu_count_1_swap_at_other sched t1 t2 j2 T' HT'ne1 HT'ne).
      rewrite (IH HT'gt). reflexivity.
Qed.

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

(* ===== Section 8: Validity/feasibility for None-to-Some swap ===== *)

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
  - rewrite swap_at_t1 in Hrun. rewrite Ht2_j2 in Hrun.
    injection Hrun as Heq. subst j''.
    split.
    + exact (proj1 Helig).
    + intro Hcomp_swap.
      apply (proj2 Helig). unfold completed in *.
      rewrite <- (swap_at_service_prefix_before_t1 sched j2 t1 t2 t1
                    (Nat.lt_le_incl t1 t2 Hlt) (Nat.le_refl t1)).
      exact Hcomp_swap.
  - destruct (Nat.eq_dec t'' t2) as [-> | Ht2ne].
    + rewrite swap_at_t2 in Hrun. rewrite Ht1_none in Hrun. discriminate.
    + rewrite (swap_at_same_outside sched t1 t2 t'' 0
                 (or_intror (conj Ht1ne Ht2ne))) in Hrun.
      assert (Helig_orig : eligible jobs 1 sched j'' t'')
        by exact (Hvalid j'' t'' 0 (Nat.lt_succ_diag_r 0) Hrun).
      split.
      * exact (proj1 Helig_orig).
      * intro Hcomp_swap. apply (proj2 Helig_orig). unfold completed in *.
        destruct (Nat.eq_dec j'' j2) as [-> | Hj2ne].
        { destruct (lt_dec t'' t1) as [Hlt_t1 | Hge_t1].
          - rewrite <- (swap_at_service_prefix_before_t1 sched j2 t1 t2 t''
                          (Nat.lt_le_incl t1 t2 Hlt) (Nat.lt_le_incl t'' t1 Hlt_t1)).
            exact Hcomp_swap.
          - destruct (lt_dec t'' t2) as [Hlt_t2 | Hge_t2].
            + assert (Hlt12' : t1 < t'') by lia.
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

(* ===== Section 9: Validity/feasibility for Some-Some swap (j <> j' given directly) ===== *)

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
      * lia.
      * exact Hj.
      * exact Hj'.
      * exact (Hfeas j HJj).
    + rewrite (swap_at_preserves_missed_deadline_other_job jobs sched j j' t t' x Hj Hj' Hxj Hxj').
      exact (Hfeas x HJx).
Qed.
