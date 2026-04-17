From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicArithmetic.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.

Import ListNotations.

(* ================================================================ *)
(* 1. A concrete periodic task set                                  *)
(* ================================================================ *)

Definition task0_ex : Task := mkTask 1 5 2.
Definition task1_ex : Task := mkTask 1 7 3.

Definition tasks_ex (tau : TaskId) : Task :=
  match tau with
  | 0 => task0_ex
  | 1 => task1_ex
  | _ => mkTask 1 100 100
  end.

Definition T_ex (tau : TaskId) : Prop := tau = 0 \/ tau = 1.

Definition offset_ex (_ : TaskId) : Time := 0.

Definition enumT_ex : list TaskId := [0; 1].

(* ================================================================ *)
(* 2. Concrete infinite jobs                                         *)
(* ================================================================ *)

(* We encode all jobs of task 0 as even JobIds and all jobs of task 1
   as odd JobIds. This yields a total global codec on (task, index). *)

Definition job_id_of_ex (tau : TaskId) (k : nat) : JobId :=
  match tau with
  | 0 => 2 * k
  | 1 => S (2 * k)
  | _ => 0
  end.

Definition jobs_ex (j : JobId) : Job :=
  if Nat.even j then
    mkJob 0 (Nat.div2 j) (5 * Nat.div2 j) 1 (5 * Nat.div2 j + 2)
  else
    mkJob 1 (Nat.div2 j) (7 * Nat.div2 j) 1 (7 * Nat.div2 j + 3).

Lemma generated_job0_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex (job_id_of_ex 0 0).
Proof.
  unfold generated_by_periodic_task, job_id_of_ex, jobs_ex, tasks_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma generated_job1_ex :
  generated_by_periodic_task tasks_ex offset_ex jobs_ex (job_id_of_ex 1 0).
Proof.
  unfold generated_by_periodic_task, job_id_of_ex, jobs_ex, tasks_ex, offset_ex.
  simpl.
  repeat split; lia.
Qed.

Lemma tasks_ex_well_formed :
  well_formed_periodic_tasks_on T_ex tasks_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; lia.
Qed.

Lemma enumT_ex_nodup :
  NoDup enumT_ex.
Proof.
  unfold enumT_ex.
  constructor.
  - simpl. intros [H | []]. discriminate.
  - constructor.
    + simpl. tauto.
    + constructor.
Qed.

Lemma enumT_ex_complete :
  forall tau, T_ex tau -> In tau enumT_ex.
Proof.
  intros tau Htau.
  destruct Htau as [-> | ->]; simpl; tauto.
Qed.

Lemma enumT_ex_sound :
  forall tau, In tau enumT_ex -> T_ex tau.
Proof.
  intros tau Htau.
  simpl in Htau.
  destruct Htau as [Htau | [Htau | []]]; subst tau.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma jobs_ex_task0 :
  forall k,
    jobs_ex (2 * k) = mkJob 0 k (5 * k) 1 (5 * k + 2).
Proof.
  intros k.
  unfold jobs_ex.
  rewrite Nat.even_mul.
  simpl.
  replace (Nat.div2 (k + (k + 0))) with k.
  2:{ replace (k + (k + 0)) with (2 * k) by lia.
      symmetry; apply Nat.div2_double. }
  reflexivity.
Qed.

Lemma jobs_ex_task1 :
  forall k,
    jobs_ex (S (2 * k)) = mkJob 1 k (7 * k) 1 (7 * k + 3).
Proof.
  intros k.
  unfold jobs_ex.
  rewrite Nat.even_succ.
  rewrite Nat.odd_mul.
  simpl.
  replace
    match k + (k + 0) with
    | 0 => 0
    | S n' => S (Nat.div2 n')
    end
  with k.
  2:{
    replace
      (match k + (k + 0) with
       | 0 => 0
       | S n' => S (Nat.div2 n')
       end)
    with (Nat.div2 (S (k + (k + 0)))) by reflexivity.
    replace (S (k + (k + 0))) with (S (2 * k)) by lia.
    symmetry; apply Nat.div2_succ_double.
  }
  reflexivity.
Qed.

Lemma jobs_ex_task0_release :
  forall k,
    job_release (jobs_ex (2 * k)) = 5 * k.
Proof.
  intros k.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma jobs_ex_task0_deadline :
  forall k,
    job_abs_deadline (jobs_ex (2 * k)) = 5 * k + 2.
Proof.
  intros k.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma jobs_ex_task0_cost :
  forall k,
    job_cost (jobs_ex (2 * k)) = 1.
Proof.
  intros k.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma jobs_ex_task1_release :
  forall k,
    job_release (jobs_ex (S (2 * k))) = 7 * k.
Proof.
  intros k.
  rewrite jobs_ex_task1.
  reflexivity.
Qed.

Lemma jobs_ex_task1_deadline :
  forall k,
    job_abs_deadline (jobs_ex (S (2 * k))) = 7 * k + 3.
Proof.
  intros k.
  rewrite jobs_ex_task1.
  reflexivity.
Qed.

Lemma jobs_ex_task1_cost :
  forall k,
    job_cost (jobs_ex (S (2 * k))) = 1.
Proof.
  intros k.
  rewrite jobs_ex_task1.
  reflexivity.
Qed.

(* ================================================================ *)
(* 3. A concrete global codec                                        *)
(* ================================================================ *)

Lemma codec_ex_sound :
  forall tau k,
    T_ex tau ->
    let j := job_id_of_ex tau k in
    job_task (jobs_ex j) = tau /\
    job_index (jobs_ex j) = k /\
    generated_by_periodic_task tasks_ex offset_ex jobs_ex j.
Proof.
  intros tau k Htau.
  destruct Htau as [-> | ->].
  - unfold job_id_of_ex.
    split.
    + rewrite jobs_ex_task0. reflexivity.
    + split.
      * rewrite jobs_ex_task0. reflexivity.
      * unfold generated_by_periodic_task, expected_release, expected_abs_deadline.
        unfold tasks_ex, offset_ex.
        rewrite jobs_ex_task0.
        unfold expected_release.
        simpl.
        split.
        -- rewrite Nat.mul_comm. reflexivity.
        -- split.
           ++ nia.
           ++ lia.
  - unfold job_id_of_ex.
    split.
    + rewrite jobs_ex_task1. reflexivity.
    + split.
      * rewrite jobs_ex_task1. reflexivity.
      * unfold generated_by_periodic_task, expected_release, expected_abs_deadline.
        unfold tasks_ex, offset_ex.
        rewrite jobs_ex_task1.
        unfold expected_release.
        simpl.
        split.
        -- rewrite Nat.mul_comm. reflexivity.
        -- split.
           ++ nia.
           ++ lia.
Qed.

Lemma codec_ex_complete :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    j = job_id_of_ex (job_task (jobs_ex j)) (job_index (jobs_ex j)).
Proof.
  intros j _.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    unfold job_id_of_ex.
    rewrite jobs_ex_task0.
    reflexivity.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    unfold job_id_of_ex.
    rewrite jobs_ex_task1.
    reflexivity.
Qed.

Definition codec_ex : PeriodicCodec T_ex tasks_ex offset_ex jobs_ex :=
  mkPeriodicCodec
    T_ex tasks_ex offset_ex jobs_ex
    job_id_of_ex
    codec_ex_sound
    codec_ex_complete.

(* ================================================================ *)
(* 4. Concrete obligations for the infinite-time wrappers           *)
(* ================================================================ *)

Definition service_slot_ex (j : JobId) : Time :=
  if Nat.even j then
    5 * Nat.div2 j
  else if Nat.eqb (Nat.div2 j mod 5) 0 then
    7 * Nat.div2 j + 1
  else
    7 * Nat.div2 j.

Definition slot_job_ex (t : Time) : option JobId :=
  if Nat.eqb (t mod 5) 0 then
    Some (job_id_of_ex 0 (t / 5))
  else if Nat.eqb (t mod 35) 1 then
    Some (job_id_of_ex 1 (t / 7))
  else if Nat.eqb (t mod 7) 0 then
    Some (job_id_of_ex 1 (t / 7))
  else
    None.

Lemma jobs_ex_in_periodic_jobset :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j.
Proof.
  intro j.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    unfold periodic_jobset.
    split.
    + left. rewrite jobs_ex_task0. reflexivity.
    + pose proof (codec_ex_sound 0 k (or_introl eq_refl)) as [_ [_ Hgen]].
      exact Hgen.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    unfold periodic_jobset.
    split.
    + right. rewrite jobs_ex_task1. reflexivity.
    + pose proof (codec_ex_sound 1 k (or_intror eq_refl)) as [_ [_ Hgen]].
      exact Hgen.
Qed.

Lemma service_slot_ex_task0 :
  forall k,
    service_slot_ex (job_id_of_ex 0 k) = 5 * k.
Proof.
  intro k.
  unfold service_slot_ex, job_id_of_ex.
  rewrite Nat.even_mul.
  simpl.
  replace (Nat.div2 (k + (k + 0))) with k.
  2:{
    replace (k + (k + 0)) with (2 * k) by lia.
    symmetry.
    apply nat_div2_double.
  }
  reflexivity.
Qed.

Lemma service_slot_ex_task1 :
  forall k,
    service_slot_ex (job_id_of_ex 1 k) =
    if Nat.eqb (k mod 5) 0 then 7 * k + 1 else 7 * k.
Proof.
  intro k.
  unfold service_slot_ex, job_id_of_ex.
  rewrite Nat.even_succ.
  rewrite Nat.odd_mul.
  simpl.
  replace
    match k + (k + 0) with
    | 0 => 0
    | S n' => S (Nat.div2 n')
    end
  with k.
  2:{
    replace
      (match k + (k + 0) with
       | 0 => 0
       | S n' => S (Nat.div2 n')
       end)
    with (Nat.div2 (S (k + (k + 0)))) by reflexivity.
    replace (S (k + (k + 0))) with (S (2 * k)) by lia.
    symmetry.
    apply nat_div2_succ_double.
  }
  reflexivity.
Qed.

Lemma slot_job_ex_task0 :
  forall k,
    slot_job_ex (5 * k) = Some (job_id_of_ex 0 k).
Proof.
  intro k.
  unfold slot_job_ex.
  rewrite <- Nat.mul_comm.
  rewrite nat_mod_mul_left by lia.
  rewrite Nat.eqb_refl.
  rewrite nat_div_mul_exact by lia.
  reflexivity.
Qed.

Lemma slot_job_ex_task1_simultaneous :
  forall q,
    slot_job_ex (35 * q + 1) = Some (job_id_of_ex 1 (5 * q)).
Proof.
  intro q.
  unfold slot_job_ex.
  assert (Hmod5eq : (35 * q + 1) mod 5 = 1).
  {
    rewrite Nat.add_mod by lia.
    replace ((35 * q) mod 5) with 0.
    2:{
      replace (35 * q) with ((7 * q) * 5) by lia.
      symmetry.
      apply nat_mod_mul_left.
      lia.
    }
    simpl.
    reflexivity.
  }
  assert (Hmod5 : (35 * q + 1) mod 5 <> 0) by (rewrite Hmod5eq; discriminate).
  destruct (Nat.eqb ((35 * q + 1) mod 5) 0) eqn:Heq5.
  - apply Nat.eqb_eq in Heq5. contradiction.
  - rewrite nat_mod_35q_plus_1_by_35.
    rewrite Nat.eqb_refl.
    rewrite nat_div_35q_plus_1_by_7.
    reflexivity.
Qed.

Lemma slot_job_ex_task1_non_simultaneous :
  forall k,
    k mod 5 <> 0 ->
    slot_job_ex (7 * k) = Some (job_id_of_ex 1 k).
Proof.
  intros k Hk.
  unfold slot_job_ex.
  assert (Hmod5nz : (7 * k) mod 5 <> 0).
  {
    remember (k mod 5) as r eqn:Hr.
    destruct r as [|r].
    - contradiction.
    - assert (Hrlt : S r < 5).
      { rewrite Hr. apply Nat.mod_upper_bound. lia. }
      rewrite Nat.mul_mod by lia.
      rewrite <- Hr.
      simpl.
      destruct r as [| [| [| [| r]]]]; simpl; try discriminate.
      lia.
  }
  destruct (Nat.eqb ((7 * k) mod 5) 0) eqn:Heq5.
  - apply Nat.eqb_eq in Heq5.
    contradiction.
  - assert (Hmod35neq : (7 * k) mod 35 <> 1).
    {
      intro Hcontra.
      assert (Hexpr : 7 * k = 35 * ((7 * k) / 35) + 1).
      {
        pose proof (Nat.div_mod (7 * k) 35) as Hdiv.
        specialize (Hdiv ltac:(lia)).
        rewrite Hcontra in Hdiv.
        lia.
      }
      assert (Hmod7 : (35 * ((7 * k) / 35) + 1) mod 7 = 0).
      {
        rewrite <- Hexpr.
        rewrite <- Nat.mul_comm.
        apply nat_mod_mul_left.
        lia.
      }
      rewrite Nat.add_mod in Hmod7 by lia.
      replace ((35 * ((7 * k) / 35)) mod 7) with 0 in Hmod7.
      2:{
        replace (35 * ((7 * k) / 35)) with ((5 * ((7 * k) / 35)) * 7) by lia.
        symmetry.
        apply nat_mod_mul_left.
        lia.
      }
      simpl in Hmod7.
      discriminate.
    }
    destruct (Nat.eqb ((7 * k) mod 35) 1) eqn:Heq35.
    + apply Nat.eqb_eq in Heq35.
      contradiction.
    + rewrite <- Nat.mul_comm.
      rewrite nat_mod_mul_left by lia.
      rewrite Nat.eqb_refl.
      rewrite nat_div_mul_exact by lia.
      reflexivity.
Qed.

Lemma jobs_ex_release_le_service_slot_ex :
  forall j,
    job_release (jobs_ex j) <= service_slot_ex j.
Proof.
  intro j.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    rewrite jobs_ex_task0_release.
    change (service_slot_ex (2 * k)) with (service_slot_ex (job_id_of_ex 0 k)).
    rewrite service_slot_ex_task0.
    lia.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    rewrite jobs_ex_task1_release.
    change (service_slot_ex (S (2 * k))) with (service_slot_ex (job_id_of_ex 1 k)).
    rewrite service_slot_ex_task1.
    destruct (Nat.eqb (k mod 5) 0); lia.
Qed.

Lemma service_slot_ex_before_deadline_ex :
  forall j,
    service_slot_ex j < job_abs_deadline (jobs_ex j).
Proof.
  intro j.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    change (service_slot_ex (2 * k)) with (service_slot_ex (job_id_of_ex 0 k)).
    rewrite service_slot_ex_task0.
    rewrite jobs_ex_task0_deadline.
    lia.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    rewrite jobs_ex_task1_deadline.
    change (service_slot_ex (S (2 * k))) with (service_slot_ex (job_id_of_ex 1 k)).
    rewrite service_slot_ex_task1.
    destruct (Nat.eqb (k mod 5) 0); lia.
Qed.

Lemma slot_job_ex_at_service_slot :
  forall j,
    slot_job_ex (service_slot_ex j) = Some j.
Proof.
  intro j.
  destruct (Nat.even j) eqn:Heven.
  - apply Nat.even_spec in Heven.
    destruct Heven as [k ->].
    change (service_slot_ex (2 * k)) with (service_slot_ex (job_id_of_ex 0 k)).
    rewrite service_slot_ex_task0.
    apply slot_job_ex_task0.
  - assert (Hodd : Nat.odd j = true).
    { rewrite <- Nat.negb_even. rewrite Heven. reflexivity. }
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    subst j.
    replace (2 * k + 1) with (S (2 * k)) by lia.
    change
      (service_slot_ex (S (2 * k)))
      with (service_slot_ex (job_id_of_ex 1 k)).
    rewrite service_slot_ex_task1.
    destruct (Nat.eqb (k mod 5) 0) eqn:Hk5.
    + apply Nat.eqb_eq in Hk5.
      assert (Hk : exists q, k = 5 * q).
      {
        exists (k / 5).
        pose proof (Nat.div_mod k 5) as Hdiv.
        specialize (Hdiv ltac:(lia)).
        rewrite Hk5 in Hdiv.
        lia.
      }
      destruct Hk as [q ->].
      replace (7 * (5 * q) + 1) with (35 * q + 1) by lia.
      rewrite slot_job_ex_task1_simultaneous.
      reflexivity.
    + apply Nat.eqb_neq in Hk5.
      exact (slot_job_ex_task1_non_simultaneous k Hk5).
Qed.

Example periodic_classical_dbf_test_by_cutoff_ex :
  dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_classical_dbf_from_cutoff_ex :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  apply dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply enumT_ex_sound.
    exact Hin.
  - exact periodic_classical_dbf_test_by_cutoff_ex.
Qed.

Example periodic_window_dbf_test_by_cutoff_ex :
  window_dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_window_dbf_from_cutoff_ex :
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  apply window_dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply enumT_ex_sound.
    exact Hin.
  - exact periodic_window_dbf_test_by_cutoff_ex.
Qed.

Definition periodic_window_dbf_bound_ex : Prop :=
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.

Definition generated_edf_busy_prefix_no_carry_in_bridge_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.

Record PeriodicEDFInfiniteConcreteObligations : Prop := {
  periodic_edf_infinite_no_carry_in_bridge :
    generated_edf_busy_prefix_no_carry_in_bridge_ex;
  periodic_edf_infinite_window_dbf_test :
    window_dbf_test_by_cutoff tasks_ex enumT_ex = true;
  periodic_edf_infinite_classical_dbf_test :
    dbf_test_by_cutoff tasks_ex enumT_ex = true
}.

Definition sched_inf_ex : Schedule :=
  generated_periodic_edf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.

Section TutorialProof.
  Hypothesis Hobl : PeriodicEDFInfiniteConcreteObligations.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss :
    ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
  Proof.
    apply periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact enumT_ex_complete.
    - exact enumT_ex_sound.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply periodic_edf_infinite_no_carry_in_bridge.
      exact Hobl.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_window_dbf_from_cutoff_ex.
  Qed.

  Theorem tutorial_periodic_edf_schedulable :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_on_with_no_carry_in_bridge.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact enumT_ex_complete.
    1: exact enumT_ex_sound.
    1: apply periodic_edf_infinite_no_carry_in_bridge; exact Hobl.
    1: exact periodic_window_dbf_from_cutoff_ex.
  Qed.

End TutorialProof.

Section TutorialClassicalProof.
  Hypothesis Hobl : PeriodicEDFInfiniteConcreteObligations.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
  Proof.
    apply periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge.
    - exact tasks_ex_well_formed.
    - exact enumT_ex_nodup.
    - exact enumT_ex_complete.
    - exact enumT_ex_sound.
    - intros τ Hin. reflexivity.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - apply periodic_edf_infinite_no_carry_in_bridge.
      exact Hobl.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact generated_job0_ex.
    - exact periodic_classical_dbf_from_cutoff_ex.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    eapply periodic_edf_schedulable_by_classical_dbf_with_no_carry_in_bridge.
    1: exact tasks_ex_well_formed.
    1: exact enumT_ex_nodup.
    1: exact enumT_ex_complete.
    1: exact enumT_ex_sound.
    1: intros τ Hin; reflexivity.
    1: apply periodic_edf_infinite_no_carry_in_bridge; exact Hobl.
    1: exact periodic_classical_dbf_from_cutoff_ex.
  Qed.
End TutorialClassicalProof.
