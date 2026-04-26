From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Analysis.Uniprocessor.DemandBound.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicWindowDemandBound.

Import ListNotations.

Lemma nodup_map_sub_const_ge :
  forall l c,
    NoDup l ->
    (forall x, In x l -> c <= x) ->
    NoDup (map (fun x => x - c) l).
Proof.
  intros l c Hnodup Hge.
  induction Hnodup as [|x l Hnotin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hin]].
      assert (c <= x) by (apply Hge; now left).
      assert (c <= y) by (apply Hge; now right).
      assert (x = y) by lia.
      subst y.
      apply Hnotin.
      exact Hin.
    + apply IH.
      intros y Hin.
      apply Hge.
      now right.
Qed.

Lemma div_ceil_minus_one_le_factor :
  forall n p k,
    0 < p ->
    n <= k * p ->
    (n + p - 1) / p <= k.
Proof.
  intros n p k Hp Hle.
  pose proof (Nat.div_mod (n + p - 1) p ltac:(lia)) as Hdivmod.
  pose proof (Nat.mod_upper_bound (n + p - 1) p ltac:(lia)) as Hmodlt.
  assert (Hlt : n + p - 1 < (S k) * p) by lia.
  nia.
Qed.

Lemma div_ceil_minus_one_mul_ge :
  forall n p,
    0 < p ->
    n <= ((n + p - 1) / p) * p.
Proof.
  intros n p Hp.
  assert (p <> 0) by lia.
  pose proof (Nat.div_mod (n + p - 1) p H) as Hdivmod.
  pose proof (Nat.mod_upper_bound (n + p - 1) p H) as Hmodlt.
  assert (Hmul :
    ((n + p - 1) / p) * p =
    (n + p - 1) - ((n + p - 1) mod p)) by lia.
  rewrite Hmul.
  assert (Hmod_le : (n + p - 1) mod p <= p - 1).
  {
    apply Nat.lt_succ_r.
    assert (HS : S (p - 1) = p) by lia.
    rewrite HS.
    exact Hmodlt.
  }
  assert (Hrewrite :
    n + p - 1 - (n + p - 1) mod p =
    n + (p - 1 - (n + p - 1) mod p)) by lia.
  rewrite Hrewrite.
  apply Nat.le_add_r.
Qed.

Lemma periodic_dbf_window_le_classical_count :
  forall tasks offset τ t1 t2,
    0 < task_period (tasks τ) ->
    length (filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))) <=
    (if (t2 - t1) <? task_relative_deadline (tasks τ) then 0
     else S (((t2 - t1) - task_relative_deadline (tasks τ)) / task_period (tasks τ))).
Proof.
  intros tasks offset τ t1 t2 Hp.
  set (p := task_period (tasks τ)).
  set (d := task_relative_deadline (tasks τ)).
  set (o := offset τ).
  set (k0 := (t1 - o + p - 1) / p).
  set (l := filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))).
  assert (Hk0_release_ge : t1 <= o + k0 * p).
  {
    subst k0 p o.
    pose proof (div_ceil_minus_one_mul_ge (t1 - offset τ) (task_period (tasks τ)) Hp) as Hceil.
    lia.
  }
  assert (Hmap_incl :
    incl (map (fun k => k - k0) l)
         (seq 0
            (if (t2 - t1) <? d then 0
             else S (((t2 - t1) - d) / p)))).
  {
    intros x Hinx.
    apply in_map_iff in Hinx.
    destruct Hinx as [k [Hx Hk]].
    subst x.
    apply filter_In in Hk.
    destruct Hk as [Hin Hwin].
    unfold periodic_index_in_window in Hwin.
    unfold expected_release in Hwin.
    unfold expected_abs_deadline in Hwin.
    rewrite andb_true_iff in Hwin.
    rewrite !Nat.leb_le in Hwin.
    destruct Hwin as [Hrel Hdl].
    rewrite in_seq in Hin.
    destruct Hin as [_ Hk_le].
    rewrite in_seq.
    assert (Hk0_le_k : k0 <= k).
    {
      subst k0 p o.
      eapply div_ceil_minus_one_le_factor.
      - exact Hp.
      - lia.
    }
    split.
    - lia.
    - assert (Hshift :
        (k - k0) * p + d <= t2 - t1).
      {
        assert (Hdl' : o + k * p + d <= t2).
        {
          subst o p d.
          exact Hdl.
        }
        assert (Hsub : k0 * p <= k * p).
        { apply Nat.mul_le_mono_r. exact Hk0_le_k. }
        replace ((k - k0) * p) with (k * p - k0 * p) by
          (symmetry; apply Nat.mul_sub_distr_r; lia).
        lia.
      }
      destruct ((t2 - t1) <? d) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. lia.
      * apply Nat.ltb_ge in Hlt.
        apply Nat.lt_succ_r.
        apply (Nat.div_le_lower_bound ((t2 - t1) - d) p (k - k0)).
        -- lia.
        -- lia.
  }
  assert (Hnodup_l : NoDup l).
  {
    unfold l.
    apply NoDup_filter.
    apply seq_NoDup.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map (fun k => k - k0) l))
      by apply List.length_map.
    eapply NoDup_incl_length.
    + apply nodup_map_sub_const_ge.
      * exact Hnodup_l.
      * intros x Hin.
        unfold l in Hin.
        apply filter_In in Hin.
        destruct Hin as [_ Hwin].
        unfold periodic_index_in_window in Hwin.
        unfold expected_release in Hwin.
        unfold expected_abs_deadline in Hwin.
        rewrite andb_true_iff in Hwin.
        rewrite !Nat.leb_le in Hwin.
        destruct Hwin as [Hrel _].
        subst k0 p o.
        eapply div_ceil_minus_one_le_factor; lia.
    + exact Hmap_incl.
  - rewrite length_seq.
    reflexivity.
Qed.

Lemma periodic_dbf_window_le_classical_dbf :
  forall tasks offset τ t1 t2,
    0 < task_period (tasks τ) ->
    periodic_dbf_window tasks offset τ t1 t2 <=
    periodic_dbf tasks τ (t2 - t1).
Proof.
  intros tasks offset τ t1 t2 Hp.
  unfold periodic_dbf_window, periodic_dbf.
  destruct ((t2 - t1) <? task_relative_deadline (tasks τ)) eqn:Hlt.
  - pose proof (periodic_dbf_window_le_classical_count tasks offset τ t1 t2 Hp) as Hcount.
    rewrite Hlt in Hcount.
    apply Nat.mul_le_mono_r with (p := task_cost (tasks τ)) in Hcount.
    simpl in Hcount.
    exact Hcount.
  - pose proof (periodic_dbf_window_le_classical_count tasks offset τ t1 t2 Hp) as Hcount.
    rewrite Hlt in Hcount.
    apply Nat.mul_le_mono_r with (p := task_cost (tasks τ)) in Hcount.
    exact Hcount.
Qed.

Lemma taskset_periodic_dbf_window_le_classical_dbf :
  forall tasks offset enumT t1 t2,
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <=
    taskset_periodic_dbf tasks enumT (t2 - t1).
Proof.
  intros tasks offset enumT t1 t2 Hp.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - apply Nat.add_le_mono.
    + apply periodic_dbf_window_le_classical_dbf.
      apply Hp. now left.
    + apply IH.
      intros τ' Hin. apply Hp. now right.
Qed.

Lemma periodic_dbf_window_zero_offset_le_classical_count :
  forall tasks offset τ t1 t2,
    offset τ = 0 ->
    0 < task_period (tasks τ) ->
    length (filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))) <=
    (if (t2 - t1) <? task_relative_deadline (tasks τ) then 0
     else S (((t2 - t1) - task_relative_deadline (tasks τ)) / task_period (tasks τ))).
Proof.
  intros tasks offset τ t1 t2 Hoff Hp.
  set (p := task_period (tasks τ)).
  set (d := task_relative_deadline (tasks τ)).
  set (k0 := (t1 + p - 1) / p).
  set (l := filter (periodic_index_in_window tasks offset τ t1 t2) (seq 0 (S t2))).
  assert (Hk0_mul_ge : t1 <= k0 * p).
  {
    subst k0 p.
    assert (task_period (tasks τ) <> 0) by lia.
    pose proof (Nat.div_mod (t1 + task_period (tasks τ) - 1) (task_period (tasks τ)) H) as Heq.
    assert (Hmod_lt :
      ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ)) <
      task_period (tasks τ)).
    { apply Nat.mod_upper_bound. lia. }
    assert (Hmul :
      ((t1 + task_period (tasks τ) - 1) / task_period (tasks τ)) *
      task_period (tasks τ) =
      (t1 + task_period (tasks τ) - 1) -
      ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ))) by lia.
    rewrite Hmul.
    assert (Hbound :
      t1 <=
      t1 + task_period (tasks τ) - 1 -
      ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ))).
    {
      assert (Hmod_le :
        ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ)) <=
        task_period (tasks τ) - 1).
      {
        apply Nat.lt_succ_r.
        assert (HS : S (task_period (tasks τ) - 1) = task_period (tasks τ)) by lia.
        rewrite HS.
        exact Hmod_lt.
      }
      replace
        (t1 + task_period (tasks τ) - 1 -
         ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ)))
        with
        (t1 +
         (task_period (tasks τ) - 1 -
          ((t1 + task_period (tasks τ) - 1) mod task_period (tasks τ)))) by lia.
      apply Nat.le_add_r.
    }
    exact Hbound.
  }
  assert (Hmap_incl :
    incl (map (fun k => k - k0) l)
         (seq 0
            (if (t2 - t1) <? d then 0
             else S (((t2 - t1) - d) / p)))).
  {
    intros x Hinx.
    apply in_map_iff in Hinx.
    destruct Hinx as [k [Hx Hk]].
    subst x.
    apply filter_In in Hk.
    destruct Hk as [Hin Hwin].
    unfold periodic_index_in_window in Hwin.
    unfold expected_release in Hwin.
    unfold expected_abs_deadline in Hwin.
    rewrite andb_true_iff in Hwin.
    rewrite !Nat.leb_le in Hwin.
    rewrite Hoff in Hwin.
    simpl in Hwin.
    destruct Hwin as [Hrel Hdl].
    rewrite in_seq in Hin.
    destruct Hin as [_ Hk_le].
    rewrite in_seq.
    split.
    - assert (Hk0_le_k : k0 <= k).
      {
        subst k0 p.
        eapply div_ceil_minus_one_le_factor; lia.
      }
      lia.
    - assert (Hk0_le_k : k0 <= k).
      {
        subst k0 p.
        eapply div_ceil_minus_one_le_factor; lia.
      }
      assert (Hshift :
        (k - k0) * p + d <= t2 - t1).
      {
        assert (Hdl' : k * p + d <= t2).
        {
          subst p d.
          unfold expected_release in Hdl.
          rewrite Hoff in Hdl.
          simpl in Hdl.
          exact Hdl.
        }
        assert (Ht1' : t1 <= k0 * p) by exact Hk0_mul_ge.
        assert (Hsub : k0 * p <= k * p).
        { apply Nat.mul_le_mono_r. exact Hk0_le_k. }
        replace ((k - k0) * p) with (k * p - k0 * p) by
          (symmetry; apply Nat.mul_sub_distr_r; lia).
        assert (Htmp : k * p - k0 * p + d <= t2 - t1) by lia.
        exact Htmp.
      }
      destruct ((t2 - t1) <? d) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. lia.
      * apply Nat.ltb_ge in Hlt.
        apply Nat.lt_succ_r.
        apply (Nat.div_le_lower_bound ((t2 - t1) - d) p (k - k0)).
        -- lia.
        -- lia.
  }
  assert (Hnodup_l : NoDup l).
  {
    unfold l.
    apply NoDup_filter.
    apply seq_NoDup.
  }
  eapply Nat.le_trans.
  - replace (length l) with (length (map (fun k => k - k0) l))
      by apply List.length_map.
    eapply NoDup_incl_length.
    + apply nodup_map_sub_const_ge.
      * exact Hnodup_l.
      * intros x Hin.
        unfold l in Hin.
        apply filter_In in Hin.
        destruct Hin as [_ Hwin].
        unfold periodic_index_in_window in Hwin.
        unfold expected_release in Hwin.
        unfold expected_abs_deadline in Hwin.
        rewrite andb_true_iff in Hwin.
        rewrite !Nat.leb_le in Hwin.
        rewrite Hoff in Hwin.
        simpl in Hwin.
        destruct Hwin as [Hrel _].
        subst k0 p.
        eapply div_ceil_minus_one_le_factor; lia.
    + exact Hmap_incl.
  - rewrite length_seq.
    reflexivity.
Qed.

Lemma zero_offset_window_dbf_le_classical_dbf :
  forall tasks offset τ t1 t2,
    offset τ = 0 ->
    0 < task_period (tasks τ) ->
    periodic_dbf_window tasks offset τ t1 t2 <=
    periodic_dbf tasks τ (t2 - t1).
Proof.
  intros tasks offset τ t1 t2 Hoff Hp.
  unfold periodic_dbf_window, periodic_dbf.
  destruct ((t2 - t1) <? task_relative_deadline (tasks τ)) eqn:Hlt.
  - 
    pose proof (periodic_dbf_window_zero_offset_le_classical_count tasks offset τ t1 t2 Hoff Hp) as Hcount.
    rewrite Hlt in Hcount.
    apply Nat.mul_le_mono_r with (p := task_cost (tasks τ)) in Hcount.
    simpl in Hcount.
    exact Hcount.
  - pose proof (periodic_dbf_window_zero_offset_le_classical_count tasks offset τ t1 t2 Hoff Hp) as Hcount.
    rewrite Hlt in Hcount.
    apply Nat.mul_le_mono_r with (p := task_cost (tasks τ)) in Hcount.
    exact Hcount.
Qed.

Lemma zero_offset_taskset_window_dbf_le_classical_dbf :
  forall tasks offset enumT t1 t2,
    (forall τ, In τ enumT -> offset τ = 0) ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    taskset_periodic_dbf_window tasks offset enumT t1 t2 <=
    taskset_periodic_dbf tasks enumT (t2 - t1).
Proof.
  intros tasks offset enumT t1 t2 Hoff Hp.
  induction enumT as [|τ enumT IH]; simpl.
  - lia.
  - apply Nat.add_le_mono.
    + apply zero_offset_window_dbf_le_classical_dbf.
      * apply Hoff. now left.
      * apply Hp. now left.
    + apply IH.
      * intros τ' Hin. apply Hoff. now right.
      * intros τ' Hin. apply Hp. now right.
Qed.
