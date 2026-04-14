From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.

Lemma expected_release_strict_mono :
  forall T tasks offset τ k1 k2,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    k1 < k2 ->
    expected_release tasks offset τ k1 <
    expected_release tasks offset τ k2.
Proof.
  intros T tasks offset τ k1 k2 Hwf Hτ Hlt.
  unfold expected_release.
  apply Nat.add_lt_mono_l.
  apply Nat.mul_lt_mono_pos_r.
  - exact (Hwf τ Hτ).
  - exact Hlt.
Qed.

Lemma expected_release_eq_implies_same_index :
  forall T tasks offset τ k1 k2,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    expected_release tasks offset τ k1 =
    expected_release tasks offset τ k2 ->
    k1 = k2.
Proof.
  intros T tasks offset τ k1 k2 Hwf Hτ Heq.
  destruct (Nat.compare_spec k1 k2) as [Hk | Hlt | Hgt].
  - exact Hk.
  - pose proof (expected_release_strict_mono T tasks offset τ k1 k2 Hwf Hτ Hlt) as Hrel.
    rewrite Heq in Hrel.
    lia.
  - pose proof (expected_release_strict_mono T tasks offset τ k2 k1 Hwf Hτ Hgt) as Hrel.
    rewrite Heq in Hrel.
    lia.
Qed.

Lemma expected_release_lt_implies_index_lt :
  forall tasks offset τ k1 k2,
    expected_release tasks offset τ k1 <
    expected_release tasks offset τ k2 ->
    k1 < k2.
Proof.
  intros tasks offset τ k1 k2 Hlt.
  destruct (le_gt_dec k2 k1) as [Hge | Hlt_idx].
  - pose proof (expected_release_monotone tasks offset τ k2 k1 Hge) as Hmono.
    lia.
  - exact Hlt_idx.
Qed.

Lemma same_task_same_index_implies_same_expected_release :
  forall tasks offset τ1 τ2 k1 k2,
    τ1 = τ2 ->
    k1 = k2 ->
    expected_release tasks offset τ1 k1 =
    expected_release tasks offset τ2 k2.
Proof.
  intros tasks offset τ1 τ2 k1 k2 Htask Hidx.
  subst. reflexivity.
Qed.

Lemma same_task_same_release_implies_same_index :
  forall T tasks offset τ1 τ2 k1 k2,
    well_formed_periodic_tasks_on T tasks ->
    T τ1 ->
    τ1 = τ2 ->
    expected_release tasks offset τ1 k1 =
    expected_release tasks offset τ2 k2 ->
    k1 = k2.
Proof.
  intros T tasks offset τ1 τ2 k1 k2 Hwf Hτ Htask Heq.
  subst τ2.
  eapply expected_release_eq_implies_same_index; eauto.
Qed.

Lemma generated_by_periodic_same_task_same_release_implies_same_index :
  forall T tasks offset jobs j1 j2,
    well_formed_periodic_tasks_on T tasks ->
    T (job_task (jobs j1)) ->
    generated_by_periodic_task tasks offset jobs j1 ->
    generated_by_periodic_task tasks offset jobs j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_release (jobs j1) = job_release (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2).
Proof.
  intros T tasks offset jobs j1 j2 Hwf Hτ Hgen1 Hgen2 Htask Hrel.
  pose proof (generated_job_release tasks offset jobs j1 Hgen1) as Hrel1.
  pose proof (generated_job_release tasks offset jobs j2 Hgen2) as Hrel2.
  eapply same_task_same_release_implies_same_index; eauto.
  rewrite <- Hrel1, <- Hrel2.
  rewrite Hrel.
  reflexivity.
Qed.
