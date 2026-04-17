From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Wf_nat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Analysis.Uniprocessor.ProcessorDemand.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFPrefixCoherence.

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

(* ================================================================ *)
(* 3. A concrete global codec                                        *)
(* ================================================================ *)

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

Definition generated_edf_backlog_free_before_release_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_backlog_free_before_release
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.

Lemma generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex :
  generated_edf_backlog_free_before_release_ex ->
  generated_edf_busy_prefix_no_carry_in_bridge_ex.
Proof.
  intros Hbacklog j Hj.
  eapply periodic_edf_no_carry_in_bridge_of_backlog_free.
  - apply generated_periodic_edf_schedule_upto_valid.
    + exact tasks_ex_well_formed.
    + exact enumT_ex_complete.
    + exact enumT_ex_sound.
  - apply Hbacklog.
    exact Hj.
Qed.

Lemma periodic_jobset_ex_normalize :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    (exists k,
      j = job_id_of_ex 0 k /\
      jobs_ex j = mkJob 0 k (5 * k) 1 (5 * k + 2)) \/
    (exists k,
      j = job_id_of_ex 1 k /\
      jobs_ex j = mkJob 1 k (7 * k) 1 (7 * k + 3)).
Proof.
  intros j Hj.
  pose proof (codec_ex_complete j Hj) as Hjcodec.
  unfold periodic_jobset, T_ex in Hj.
  destruct Hj as [Htask _].
  destruct Htask as [Htask | Htask].
  - left.
    exists (job_index (jobs_ex j)).
    split.
    + rewrite <- Htask.
      exact Hjcodec.
    + assert (Hjid : j = job_id_of_ex 0 (job_index (jobs_ex j))).
      { rewrite <- Htask. exact Hjcodec. }
      rewrite Hjid.
      unfold job_id_of_ex.
      rewrite jobs_ex_task0.
      reflexivity.
  - right.
    exists (job_index (jobs_ex j)).
    split.
    + rewrite <- Htask.
      exact Hjcodec.
    + assert (Hjid : j = job_id_of_ex 1 (job_index (jobs_ex j))).
      { rewrite <- Htask. exact Hjcodec. }
      rewrite Hjid.
      unfold job_id_of_ex.
      rewrite jobs_ex_task1.
      reflexivity.
Qed.

Lemma job_release_of_task0_ex :
  forall j k,
    j = job_id_of_ex 0 k ->
    job_release (jobs_ex j) = 5 * k.
Proof.
  intros j k Hj.
  rewrite Hj.
  unfold job_id_of_ex.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma job_release_of_task1_ex :
  forall j k,
    j = job_id_of_ex 1 k ->
    job_release (jobs_ex j) = 7 * k.
Proof.
  intros j k Hj.
  rewrite Hj.
  unfold job_id_of_ex.
  rewrite jobs_ex_task1.
  reflexivity.
Qed.

Lemma job_deadline_of_task0_ex :
  forall j k,
    j = job_id_of_ex 0 k ->
    job_abs_deadline (jobs_ex j) = 5 * k + 2.
Proof.
  intros j k Hj.
  rewrite Hj.
  unfold job_id_of_ex.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma job_deadline_of_task1_ex :
  forall j k,
    j = job_id_of_ex 1 k ->
    job_abs_deadline (jobs_ex j) = 7 * k + 3.
Proof.
  intros j k Hj.
  rewrite Hj.
  unfold job_id_of_ex.
  rewrite jobs_ex_task1.
  reflexivity.
Qed.

Lemma task0_release_lt_implies_index_lt_ex :
  forall k1 k2,
    5 * k1 < 5 * k2 ->
    k1 < k2.
Proof.
  intros k1 k2 Hlt.
  nia.
Qed.

Lemma task1_release_lt_implies_index_lt_ex :
  forall k1 k2,
    7 * k1 < 7 * k2 ->
    k1 < k2.
Proof.
  intros k1 k2 Hlt.
  nia.
Qed.

Lemma task0_release_lt_task1_release_implies_task0_completed_by_task1_release_ex :
  forall k1 k2,
    5 * k1 < 7 * k2 ->
    5 * k1 + 1 <= 7 * k2.
Proof.
  intros k1 k2 Hlt.
  lia.
Qed.

Lemma collision_release_ex :
  forall k m,
    7 * k = 5 * m ->
    exists q, k = 5 * q /\ m = 7 * q.
Proof.
  intros k m Heq.
  assert (Hdiv5_7k : Nat.divide 5 (7 * k)).
  { exists m. nia. }
  assert (Hgcd : Nat.gcd 5 7 = 1) by reflexivity.
  pose proof (Nat.gauss 5 7 k Hdiv5_7k Hgcd) as Hdiv5_k.
  destruct Hdiv5_k as [q Hk].
  exists q.
  split.
  - nia.
  - nia.
Qed.

Lemma noncollision_task1_release_ex :
  forall k,
    (forall q, k <> 5 * q) ->
    forall m, 7 * k <> 5 * m.
Proof.
  intros k Hnc m Heq.
  destruct (collision_release_ex k m Heq) as [q [Hk _]].
  apply (Hnc q).
  exact Hk.
Qed.

Lemma task1_collision_dec_ex :
  forall k,
    { q : nat | k = 5 * q } +
    { forall q, k <> 5 * q }.
Proof.
  intro k.
  destruct (Nat.eq_dec (k mod 5) 0) as [Hmod | Hmod].
  - left.
    exists (k / 5).
    pose proof (Nat.div_mod k 5 ltac:(lia)) as Hdiv.
    lia.
  - right.
    intros q Heq.
    apply Hmod.
    rewrite Heq.
    rewrite Nat.mul_comm.
    replace ((q * 5) mod 5) with 0 by (symmetry; apply Nat.mod_mul; lia).
    reflexivity.
Qed.

Lemma noncollision_task1_release_lt_task0_release_implies_completion_by_task0_release_ex :
  forall k1 k2,
    (forall q, k1 <> 5 * q) ->
    7 * k1 < 5 * k2 ->
    7 * k1 + 1 <= 5 * k2.
Proof.
  intros k1 k2 Hnc Hlt.
  destruct (Nat.eq_dec (7 * k1 + 1) (5 * k2)) as [Heq | Hneq].
  - lia.
  - assert (7 * k1 + 1 < 5 * k2 \/ 5 * k2 < 7 * k1 + 1) by lia.
    destruct H as [Hsmall | Hlarge].
    + lia.
    + exfalso.
      assert (7 * k1 = 5 * k2 - 1) by lia.
      assert (Hdiv5 : Nat.divide 5 (7 * k1)).
      { exists (k2 - 1). lia. }
      destruct Hdiv5 as [m Hm].
      apply (noncollision_task1_release_ex k1 Hnc m).
      nia.
Qed.

Lemma collision_task1_release_lt_task0_release_implies_completion_by_task0_release_ex :
  forall q k,
    35 * q < 5 * k ->
    35 * q + 2 <= 5 * k.
Proof.
  intros q k Hlt.
  lia.
Qed.

Lemma generated_periodic_edf_schedule_upto_valid_ex :
  forall H,
    valid_schedule jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex).
Proof.
  intro H.
  apply generated_periodic_edf_schedule_upto_valid.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - exact enumT_ex_sound.
Qed.

Lemma generated_periodic_edf_schedule_upto_scheduler_rel_ex :
  forall H,
    scheduler_rel
      (edf_scheduler
         (enum_candidates_of
            (enum_periodic_jobs_upto
               T_ex tasks_ex offset_ex jobs_ex H enumT_ex
               (periodic_finite_horizon_codec_of
                  T_ex tasks_ex offset_ex jobs_ex H codec_ex))))
      jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex).
Proof.
  intro H.
  apply generated_periodic_edf_schedule_upto_scheduler_rel.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - exact enumT_ex_sound.
Qed.

Lemma generated_edf_upto_cpu0_eq_choose_ex :
  forall H t,
    generated_periodic_edf_schedule_upto
      T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex t 0 =
    choose_edf jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      t
      (enum_periodic_jobs_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex
         (periodic_finite_horizon_codec_of
            T_ex tasks_ex offset_ex jobs_ex H codec_ex)).
Proof.
  intros H t.
  set (enumJ :=
         enum_periodic_jobs_upto
           T_ex tasks_ex offset_ex jobs_ex H enumT_ex
           (periodic_finite_horizon_codec_of
              T_ex tasks_ex offset_ex jobs_ex H codec_ex)).
  exact
    (single_cpu_algorithm_eq_cpu0
       edf_generic_spec
       (enum_candidates_of enumJ)
       jobs_ex
       (generated_periodic_edf_schedule_upto
          T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
       t
       (generated_periodic_edf_schedule_upto_scheduler_rel_ex H)).
Qed.

Lemma candidate_in_generated_edf_upto_ex_normalize :
  forall H j,
    In j
       (enum_periodic_jobs_upto
          T_ex tasks_ex offset_ex jobs_ex H enumT_ex
          (periodic_finite_horizon_codec_of
             T_ex tasks_ex offset_ex jobs_ex H codec_ex)) ->
    (exists k,
      j = job_id_of_ex 0 k /\
      jobs_ex j = mkJob 0 k (5 * k) 1 (5 * k + 2)) \/
    (exists k,
      j = job_id_of_ex 1 k /\
      jobs_ex j = mkJob 1 k (7 * k) 1 (7 * k + 3)).
Proof.
  intros H j Hin.
  apply periodic_jobset_ex_normalize.
  eapply periodic_jobset_upto_implies_periodic_jobset.
  eapply enum_periodic_jobs_upto_sound.
  - exact enumT_ex_sound.
  - exact Hin.
Qed.

Lemma periodic_jobset_job0_ex :
  forall k,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex (job_id_of_ex 0 k).
Proof.
  intro k.
  pose proof (codec_ex_sound 0 k (or_introl eq_refl)) as [Htask [_ Hgen]].
  split.
  - rewrite Htask. left. reflexivity.
  - exact Hgen.
Qed.

Lemma periodic_jobset_job1_ex :
  forall k,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex (job_id_of_ex 1 k).
Proof.
  intro k.
  pose proof (codec_ex_sound 1 k (or_intror eq_refl)) as [Htask [_ Hgen]].
  split.
  - rewrite Htask. right. reflexivity.
  - exact Hgen.
Qed.

Lemma task0_job_in_generated_edf_upto_ex :
  forall H k,
    5 * k < H ->
    In (job_id_of_ex 0 k)
       (enum_periodic_jobs_upto
          T_ex tasks_ex offset_ex jobs_ex H enumT_ex
          (periodic_finite_horizon_codec_of
             T_ex tasks_ex offset_ex jobs_ex H codec_ex)).
Proof.
  intros H k Hrel.
  eapply enum_periodic_jobs_upto_complete.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - split.
    + unfold job_id_of_ex.
      rewrite jobs_ex_task0.
      left. reflexivity.
    + split.
      * exact
          (proj2 (proj2 (codec_ex_sound 0 k (or_introl eq_refl)))).
      * rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
        exact Hrel.
Qed.

Lemma task1_job_in_generated_edf_upto_ex :
  forall H k,
    7 * k < H ->
    In (job_id_of_ex 1 k)
       (enum_periodic_jobs_upto
          T_ex tasks_ex offset_ex jobs_ex H enumT_ex
          (periodic_finite_horizon_codec_of
             T_ex tasks_ex offset_ex jobs_ex H codec_ex)).
Proof.
  intros H k Hrel.
  eapply enum_periodic_jobs_upto_complete.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - split.
    + unfold job_id_of_ex.
      rewrite jobs_ex_task1.
      right. reflexivity.
    + split.
      * exact
          (proj2 (proj2 (codec_ex_sound 1 k (or_intror eq_refl)))).
      * rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
        exact Hrel.
Qed.

Lemma task0_job_eligible_at_release_ex :
  forall H k,
    5 * k < H ->
    eligible jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      (job_id_of_ex 0 k)
      (5 * k).
Proof.
  intros H k Hrel.
  split.
  - unfold released.
    rewrite (job_release_of_task0_ex _ _ eq_refl).
    lia.
  - apply not_completed_iff_service_lt_cost.
    pose proof (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl) as Hrelease0.
    rewrite <- Hrelease0.
    rewrite (service_at_release_zero
               jobs_ex 1
               (generated_periodic_edf_schedule_upto
                  T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
               (job_id_of_ex 0 k)).
    + unfold job_id_of_ex.
      rewrite jobs_ex_task0.
      simpl.
      lia.
    + apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Lemma task1_job_eligible_at_release_ex :
  forall H k,
    7 * k < H ->
    eligible jobs_ex 1
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      (job_id_of_ex 1 k)
      (7 * k).
Proof.
  intros H k Hrel.
  split.
  - unfold released.
    rewrite (job_release_of_task1_ex _ _ eq_refl).
    lia.
  - apply not_completed_iff_service_lt_cost.
    pose proof (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl) as Hrelease1.
    rewrite <- Hrelease1.
    rewrite (service_at_release_zero
               jobs_ex 1
               (generated_periodic_edf_schedule_upto
                  T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
               (job_id_of_ex 1 k)).
    + unfold job_id_of_ex.
      rewrite jobs_ex_task1.
      simpl.
      lia.
    + apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Definition sched_upto_ex (H : Time) : Schedule :=
  generated_periodic_edf_schedule_upto
    T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex.

Lemma task0_completed_if_scheduled_at_release_ex :
  forall H k,
    5 * k + 1 < H ->
    sched_upto_ex H (5 * k) 0 = Some (job_id_of_ex 0 k) ->
    completed jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 0 k) (5 * k + 1).
Proof.
  intros H k Hbound Hrun.
  unfold completed.
  replace (5 * k + 1) with (S (5 * k)) by lia.
  rewrite service_job_step_uni.
  assert (Hruns :
    runs_on (sched_upto_ex H) (job_id_of_ex 0 k) (5 * k) 0 = true).
  { apply runs_on_true_iff. exact Hrun. }
  rewrite Hruns.
  pose proof (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl) as Hrel.
  rewrite <- Hrel.
  rewrite (service_at_release_zero jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 0 k)).
  - unfold job_id_of_ex.
    rewrite jobs_ex_task0.
    simpl.
    lia.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Lemma task1_completed_if_scheduled_at_release_ex :
  forall H k,
    7 * k + 1 < H ->
    sched_upto_ex H (7 * k) 0 = Some (job_id_of_ex 1 k) ->
    completed jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 k) (7 * k + 1).
Proof.
  intros H k Hbound Hrun.
  unfold completed.
  replace (7 * k + 1) with (S (7 * k)) by lia.
  rewrite service_job_step_uni.
  assert (Hruns :
    runs_on (sched_upto_ex H) (job_id_of_ex 1 k) (7 * k) 0 = true).
  { apply runs_on_true_iff. exact Hrun. }
  rewrite Hruns.
  pose proof (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl) as Hrel.
  rewrite <- Hrel.
  rewrite (service_at_release_zero jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 k)).
  - unfold job_id_of_ex.
    rewrite jobs_ex_task1.
    simpl.
    lia.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Lemma task1_completed_if_not_scheduled_at_release_then_at_next_ex :
  forall H q,
    35 * q + 2 < H ->
    sched_upto_ex H (35 * q) 0 = Some (job_id_of_ex 0 (7 * q)) ->
    sched_upto_ex H (35 * q + 1) 0 = Some (job_id_of_ex 1 (5 * q)) ->
    completed jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 (5 * q)) (35 * q + 2).
Proof.
  intros H q Hbound Hrun0 Hrun1.
  unfold completed.
  replace (35 * q + 2) with (S (35 * q + 1)) by lia.
  rewrite service_job_step_uni.
  assert (Hruns1 :
    runs_on (sched_upto_ex H) (job_id_of_ex 1 (5 * q)) (35 * q + 1) 0 = true).
  { apply runs_on_true_iff. exact Hrun1. }
  rewrite Hruns1.
  replace (35 * q + 1) with (S (35 * q)) by lia.
  rewrite service_job_step_uni.
  assert (Hnotruns0 :
    runs_on (sched_upto_ex H) (job_id_of_ex 1 (5 * q)) (35 * q) 0 = false).
  {
    apply runs_on_false_iff.
    intro Heq.
    rewrite Hrun0 in Heq.
    unfold job_id_of_ex in Heq.
    inversion Heq.
    lia.
  }
  rewrite Hnotruns0.
  replace (35 * q) with (7 * (5 * q)) by lia.
  pose proof (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl) as Hrel.
  rewrite <- Hrel.
  rewrite (service_at_release_zero jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 (5 * q))).
  - unfold job_id_of_ex.
    rewrite jobs_ex_task1.
    simpl.
    lia.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Lemma task1_job_eligible_one_tick_after_collision_ex :
  forall H q,
    35 * q + 2 < H ->
    sched_upto_ex H (35 * q) 0 = Some (job_id_of_ex 0 (7 * q)) ->
    eligible jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 (5 * q)) (35 * q + 1).
Proof.
  intros H q Hbound Hrun0.
  split.
  - unfold released.
    replace (35 * q + 1) with (7 * (5 * q) + 1) by lia.
    pose proof (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl) as Hrel.
    rewrite Hrel.
    lia.
  - apply not_completed_iff_service_lt_cost.
    replace (35 * q + 1) with (S (35 * q)) by lia.
    rewrite service_job_step_uni.
    assert (Hnotruns0 :
      runs_on (sched_upto_ex H) (job_id_of_ex 1 (5 * q)) (35 * q) 0 = false).
    {
      apply runs_on_false_iff.
      intro Heq.
      rewrite Hrun0 in Heq.
      unfold job_id_of_ex in Heq.
      inversion Heq.
      lia.
    }
    rewrite Hnotruns0.
    replace (35 * q) with (7 * (5 * q)) by lia.
    pose proof (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl) as Hrel.
    rewrite <- Hrel.
    rewrite (service_at_release_zero jobs_ex 1 (sched_upto_ex H) (job_id_of_ex 1 (5 * q))).
    + unfold job_id_of_ex.
      rewrite jobs_ex_task1.
      simpl.
      lia.
    + apply generated_periodic_edf_schedule_upto_valid_ex.
Qed.

Definition sched_inf_ex : Schedule :=
  generated_periodic_edf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.

Inductive completion_target_ex : JobId -> Time -> Prop :=
| completion_target_task0_ex :
    forall k,
      completion_target_ex (job_id_of_ex 0 k) (5 * k + 1)
| completion_target_task1_noncollision_ex :
    forall k,
      (forall q, k <> 5 * q) ->
      completion_target_ex (job_id_of_ex 1 k) (7 * k + 1)
| completion_target_task1_collision_ex :
    forall q,
      completion_target_ex (job_id_of_ex 1 (5 * q)) (35 * q + 2).

Lemma periodic_job_has_completion_target_ex :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    exists t, completion_target_ex j t.
Proof.
  intros j Hj.
  pose proof (periodic_jobset_ex_normalize j Hj) as Hnorm.
  destruct Hnorm as [[k [Hjid _]] | [k [Hjid _]]].
  - subst j.
    exists (5 * k + 1).
    constructor.
  - subst j.
    destruct (task1_collision_dec_ex k) as [[q Hq] | Hnc].
    + subst k.
      exists (35 * q + 2).
      constructor.
    + exists (7 * k + 1).
      constructor.
      exact Hnc.
Qed.

Lemma completion_target_before_task0_release_ex :
  forall y ty k,
    completion_target_ex y ty ->
    job_release (jobs_ex y) < 5 * k ->
    ty <= 5 * k.
Proof.
  intros y ty k Htarget Hrel.
  destruct Htarget as [k'|k' Hnc|q].
  - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
    apply task0_release_lt_implies_index_lt_ex in Hrel.
    lia.
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
    exact
      (noncollision_task1_release_lt_task0_release_implies_completion_by_task0_release_ex
         k' k Hnc Hrel).
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl) in Hrel.
    replace (7 * (5 * q)) with (35 * q) in Hrel by lia.
    exact
      (collision_task1_release_lt_task0_release_implies_completion_by_task0_release_ex
         q k Hrel).
Qed.

Lemma completion_target_before_task1_release_ex :
  forall y ty k,
    completion_target_ex y ty ->
    job_release (jobs_ex y) < 7 * k ->
    ty <= 7 * k.
Proof.
  intros y ty k Htarget Hrel.
  destruct Htarget as [k'|k' Hnc|q].
  - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
    exact
      (task0_release_lt_task1_release_implies_task0_completed_by_task1_release_ex
         k' k Hrel).
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
    apply task1_release_lt_implies_index_lt_ex in Hrel.
    lia.
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl) in Hrel.
    lia.
Qed.

Lemma completion_target_before_collision_followup_ex :
  forall y ty q,
    completion_target_ex y ty ->
    job_release (jobs_ex y) < 35 * q ->
    ty <= 35 * q + 1.
Proof.
  intros y ty q Htarget Hrel.
  destruct Htarget as [k'|k' Hnc|q'].
  - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
    lia.
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
    lia.
  - rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q')) (5 * q') eq_refl) in Hrel.
    lia.
Qed.

Lemma completion_target_before_current_release_ex :
  forall j y ty,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    completion_target_ex y ty ->
    job_release (jobs_ex y) < job_release (jobs_ex j) ->
    ty <= job_release (jobs_ex j).
Proof.
  intros j y ty Hj Hty Hyrel.
  pose proof (periodic_jobset_ex_normalize j Hj) as Hjnorm.
  destruct Hjnorm as [[k [Hj0 _]] | [k [Hj1 _]]].
  { subst j.
    rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl) in Hyrel |- *.
    exact (completion_target_before_task0_release_ex y ty k Hty Hyrel). }
  { subst j.
    rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl) in Hyrel |- *.
    exact (completion_target_before_task1_release_ex y ty k Hty Hyrel). }
Qed.

Lemma task0_scheduled_at_release_of_earlier_completion_ex :
  forall H k,
    5 * k + 1 < H ->
    (forall y,
       periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
       job_release (jobs_ex y) < 5 * k ->
       completed jobs_ex 1 (sched_upto_ex H) y (5 * k)) ->
    sched_upto_ex H (5 * k) 0 = Some (job_id_of_ex 0 k).
Proof.
  intros H k Hbound Hprev.
  unfold sched_upto_ex.
  rewrite generated_edf_upto_cpu0_eq_choose_ex.
  apply choose_edf_unique_min.
  - apply task0_job_in_generated_edf_upto_ex. lia.
  - apply task0_job_eligible_at_release_ex. lia.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' [Hy _]] | [k' [Hy _]]].
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 0 k') (5 * k) Helig) as Hrel.
      destruct (Nat.lt_ge_cases k' k) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job0_ex k').
        -- rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl). lia.
      * destruct (Nat.eq_dec k' k) as [-> | Hneqk].
        -- exfalso. apply Hneq. reflexivity.
        -- rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
           lia.
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 1 k') (5 * k) Helig) as Hrel.
      destruct (Nat.lt_ge_cases (7 * k') (5 * k)) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job1_ex k').
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl). exact Hlt.
      * destruct (Nat.eq_dec (7 * k') (5 * k)) as [Heq | Hgt].
        -- rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k') k' eq_refl).
           rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
           lia.
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
           lia.
Qed.

Lemma task1_scheduled_at_release_of_earlier_completion_ex :
  forall H k,
    (forall q, k <> 5 * q) ->
    7 * k + 1 < H ->
    (forall y,
       periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
       job_release (jobs_ex y) < 7 * k ->
       completed jobs_ex 1 (sched_upto_ex H) y (7 * k)) ->
    sched_upto_ex H (7 * k) 0 = Some (job_id_of_ex 1 k).
Proof.
  intros H k Hnc Hbound Hprev.
  unfold sched_upto_ex.
  rewrite generated_edf_upto_cpu0_eq_choose_ex.
  apply choose_edf_unique_min.
  - apply task1_job_in_generated_edf_upto_ex. lia.
  - apply task1_job_eligible_at_release_ex. lia.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' [Hy _]] | [k' [Hy _]]].
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 0 k') (7 * k) Helig) as Hrel.
      destruct (Nat.lt_ge_cases (5 * k') (7 * k)) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job0_ex k').
        -- rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl). exact Hlt.
      * rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
        destruct (Nat.eq_dec (5 * k') (7 * k)) as [Heq | Hneqrel].
        -- exfalso.
           apply (noncollision_task1_release_ex k Hnc k').
           symmetry; exact Heq.
        -- lia.
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 1 k') (7 * k) Helig) as Hrel.
      destruct (Nat.lt_ge_cases k' k) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job1_ex k').
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl). lia.
      * destruct (Nat.eq_dec k' k) as [-> | Hneqk].
        -- exfalso. apply Hneq. reflexivity.
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
           lia.
Qed.

Lemma task1_scheduled_after_collision_of_earlier_completion_ex :
  forall H q,
    35 * q + 2 < H ->
    sched_upto_ex H (35 * q) 0 = Some (job_id_of_ex 0 (7 * q)) ->
    (forall y,
       periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
       job_release (jobs_ex y) < 35 * q ->
       completed jobs_ex 1 (sched_upto_ex H) y (35 * q + 1)) ->
    sched_upto_ex H (35 * q + 1) 0 = Some (job_id_of_ex 1 (5 * q)).
Proof.
  intros H q Hbound Hrun0 Hprev.
  unfold sched_upto_ex.
  rewrite generated_edf_upto_cpu0_eq_choose_ex.
  apply choose_edf_unique_min.
  - apply task1_job_in_generated_edf_upto_ex. lia.
  - apply task1_job_eligible_one_tick_after_collision_ex; assumption.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' [Hy _]] | [k' [Hy _]]].
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 0 k') (35 * q + 1) Helig) as Hrel.
      destruct (Nat.lt_ge_cases (5 * k') (35 * q)) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job0_ex k').
        -- rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl). exact Hlt.
      * destruct (Nat.eq_dec (5 * k') (35 * q)) as [Heq | Hgt].
        -- replace k' with (7 * q) in * by lia.
           exfalso.
           apply (proj2 Helig).
           replace (35 * q) with (5 * (7 * q)) in Hrun0 by lia.
           replace (35 * q + 1) with (5 * (7 * q) + 1) by lia.
           eapply task0_completed_if_scheduled_at_release_ex.
           ++ lia.
           ++ exact Hrun0.
        -- rewrite (job_release_of_task0_ex (job_id_of_ex 0 k') k' eq_refl) in Hrel.
           lia.
    + subst y.
      pose proof (eligible_after_release jobs_ex 1 (sched_upto_ex H)
                    (job_id_of_ex 1 k') (35 * q + 1) Helig) as Hrel.
      destruct (Nat.lt_ge_cases k' (5 * q)) as [Hlt | Hge].
      * exfalso.
        apply (proj2 Helig).
        apply Hprev.
        -- exact (periodic_jobset_job1_ex k').
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl). lia.
      * destruct (Nat.eq_dec k' (5 * q)) as [-> | Hneqk].
        -- exfalso. apply Hneq. reflexivity.
        -- rewrite (job_release_of_task1_ex (job_id_of_ex 1 k') k' eq_refl) in Hrel.
           lia.
Qed.

Lemma completed_at_completion_target_ex :
  forall H j t,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    completion_target_ex j t ->
    t < H ->
    completed jobs_ex 1 (sched_upto_ex H) j t.
Proof.
  intros H j t Hj Htarget Hbound.
  set (P :=
         fun r =>
           forall j t,
             periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
             job_release (jobs_ex j) = r ->
             completion_target_ex j t ->
             t < H ->
             completed jobs_ex 1 (sched_upto_ex H) j t).
  assert (HP : P (job_release (jobs_ex j))).
  {
    unfold P.
    apply (well_founded_induction
             lt_wf
             (fun r =>
                forall j t,
                  periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
                  job_release (jobs_ex j) = r ->
                  completion_target_ex j t ->
                  t < H ->
                  completed jobs_ex 1 (sched_upto_ex H) j t)).
    intros r IH j0 t0 Hj0 Hrel0 Htarget0 Hbound0.
    inversion Htarget0; subst; clear Htarget0.
    - 
      eapply task0_completed_if_scheduled_at_release_ex; [exact Hbound0|].
      apply task0_scheduled_at_release_of_earlier_completion_ex; [exact Hbound0|].
      intros y Hy Hyrel.
      destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
      assert (Hty_le : ty <= 5 * k).
      { eapply completion_target_before_task0_release_ex; eauto. }
      assert (Hty_lt_H : ty < H) by lia.
      pose proof
        (IH
           (job_release (jobs_ex y))
           ltac:(rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl); exact Hyrel)
           y ty Hy eq_refl Hty Hty_lt_H)
        as Hdone.
      eapply completed_monotone; eauto.
    - 
      eapply task1_completed_if_scheduled_at_release_ex; [exact Hbound0|].
      apply task1_scheduled_at_release_of_earlier_completion_ex.
      + match goal with
        | Hnc_local : (forall q0, k <> 5 * q0) |- _ => exact Hnc_local
        end.
      + exact Hbound0.
      + 
      intros y Hy Hyrel.
      destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
      assert (Hty_le : ty <= 7 * k).
      { eapply completion_target_before_task1_release_ex; eauto. }
      assert (Hty_lt_H : ty < H) by lia.
      pose proof
        (IH
           (job_release (jobs_ex y))
           ltac:(rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl); exact Hyrel)
           y ty Hy eq_refl Hty Hty_lt_H)
        as Hdone.
      eapply completed_monotone; eauto.
    - 
      pose proof
        (task0_scheduled_at_release_of_earlier_completion_ex
           H (7 * q)
           ltac:(lia)
           (fun y Hy Hyrel =>
              let Hty_ex := periodic_job_has_completion_target_ex y Hy in
              match Hty_ex with
              | ex_intro _ ty Hty =>
                  let Hty_le :=
                    completion_target_before_task0_release_ex y ty (7 * q) Hty
                      ltac:(replace (35 * q) with (5 * (7 * q)) in Hyrel by lia; exact Hyrel) in
                  let Hty_lt_H : ty < H := ltac:(lia) in
                  let Hdone :=
                    IH
                      (job_release (jobs_ex y))
                      ltac:(
                        rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl);
                        replace (7 * (5 * q)) with (5 * (7 * q)) by lia;
                        replace (5 * (7 * q)) with (35 * q) in Hyrel by lia;
                        exact Hyrel)
                      y ty Hy eq_refl Hty Hty_lt_H in
                  completed_monotone jobs_ex 1 (sched_upto_ex H) y ty (5 * (7 * q)) Hty_le Hdone
              end))
        as Hrun0'.
      assert (Hrun0 :
        sched_upto_ex H (35 * q) 0 = Some (job_id_of_ex 0 (7 * q))).
      {
        replace (35 * q) with (5 * (7 * q)) by lia.
        exact Hrun0'.
      }
      eapply task1_completed_if_not_scheduled_at_release_then_at_next_ex.
      { exact Hbound0. }
      { exact Hrun0. }
      {
        apply task1_scheduled_after_collision_of_earlier_completion_ex; [exact Hbound0|exact Hrun0|].
        intros y Hy Hyrel.
        destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
        assert (Hty_le : ty <= 35 * q + 1).
        { eapply completion_target_before_collision_followup_ex; eauto. }
        assert (Hty_lt_H : ty < H) by lia.
        pose proof
          (IH
             (job_release (jobs_ex y))
             ltac:(
               rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl);
               replace (7 * (5 * q)) with (35 * q) by lia;
               exact Hyrel)
             y ty Hy eq_refl Hty Hty_lt_H)
          as Hdone.
        eapply completed_monotone; eauto.
      }
  }
  exact (HP j t Hj eq_refl Htarget Hbound).
Qed.

Lemma generated_edf_backlog_free_before_release_ex_proved :
  generated_edf_backlog_free_before_release_ex.
Proof.
  intros j Hj.
  eapply periodic_edf_backlog_free_before_release_of_earlier_completion.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
  - exact Hj.
  - intros y Hy Hyrel.
    destruct (periodic_job_has_completion_target_ex y
                (conj
                   (periodic_jobset_deadline_between_implies_task_in_scope
                      T_ex tasks_ex offset_ex jobs_ex 0
                      (job_abs_deadline (jobs_ex j)) y Hy)
                   (periodic_jobset_deadline_between_implies_generated
                      T_ex tasks_ex offset_ex jobs_ex 0
                      (job_abs_deadline (jobs_ex j)) y Hy))) as [ty Hty].
    assert (Hty_le :
      ty <= job_release (jobs_ex j)).
    {
      eapply completion_target_before_current_release_ex; eauto.
    }
    assert (Hty_lt_H :
      ty < S (job_abs_deadline (jobs_ex j))).
    {
      pose proof (periodic_jobset_ex_normalize j Hj) as Hjnorm.
      destruct Hjnorm as [[k [Hj0 _]] | [k [Hj1 _]]]; subst j.
      - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl) in Hty_le.
        rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
        lia.
      - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl) in Hty_le.
        rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
        lia.
    }
    assert (Hpy :
      periodic_jobset T_ex tasks_ex offset_ex jobs_ex y).
    {
      split.
      - exact
          (periodic_jobset_deadline_between_implies_task_in_scope
             T_ex tasks_ex offset_ex jobs_ex 0
             (job_abs_deadline (jobs_ex j)) y Hy).
      - exact
          (periodic_jobset_deadline_between_implies_generated
             T_ex tasks_ex offset_ex jobs_ex 0
             (job_abs_deadline (jobs_ex j)) y Hy).
    }
    pose proof
      (completed_at_completion_target_ex
         (S (job_abs_deadline (jobs_ex j))) y ty Hpy Hty Hty_lt_H) as Hdone.
    eapply completed_monotone; eauto.
Qed.

Section TutorialClassicalProof.
  Definition tutorial_infinite_classical_obligations :
    PeriodicEDFConcreteInfiniteClassicalObligations
      T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.
  Proof.
    pose proof
      (generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex
         generated_edf_backlog_free_before_release_ex_proved)
      as Hbridge.
    refine
      {| periodic_edf_concrete_infinite_tasks_wf := tasks_ex_well_formed;
         periodic_edf_concrete_infinite_enumT_nodup := enumT_ex_nodup;
         periodic_edf_concrete_infinite_enumT_complete := enumT_ex_complete;
         periodic_edf_concrete_infinite_enumT_sound := enumT_ex_sound;
         periodic_edf_concrete_infinite_offset_zero := _;
         periodic_edf_concrete_infinite_no_carry_in_bridge := Hbridge;
         periodic_edf_concrete_infinite_dbf_test_by_cutoff :=
           periodic_classical_dbf_test_by_cutoff_ex |}.
    intros τ _.
    reflexivity.
  Qed.

  Theorem tutorial_periodic_edf_job0_no_deadline_miss_by_classical_dbf :
    ~ missed_deadline jobs_ex 1 sched_inf_ex 0.
  Proof.
    pose proof tutorial_infinite_classical_obligations as Hobl.
    destruct Hobl as [Hwf Hnodup Hcomplete Hsound Hoff Hbridge' Hdbf].
    pose proof
      (global_periodic_job_id_of_sound
         T_ex tasks_ex offset_ex jobs_ex codec_ex 0 0
         (or_introl eq_refl)) as [_ [_ Hgen0]].
    apply periodic_edf_no_deadline_miss_from_classical_dbf_with_no_carry_in_bridge.
    - exact Hwf.
    - exact Hnodup.
    - exact Hcomplete.
    - exact Hsound.
    - exact Hoff.
    - unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact Hgen0.
    - apply Hbridge'.
      unfold periodic_jobset, T_ex.
      split.
      + left. reflexivity.
      + exact Hgen0.
    - eapply dbf_check_by_cutoff.
      + exact Hnodup.
      + intros τ Hin.
        apply Hwf.
        apply Hsound.
        exact Hin.
      + exact Hdbf.
  Qed.

  Theorem tutorial_periodic_edf_schedulable :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    apply periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations.
    exact tutorial_infinite_classical_obligations.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
    schedulable_by_on
      (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
      (edf_scheduler
         (periodic_candidates_before
            T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
      jobs_ex 1.
  Proof.
    exact tutorial_periodic_edf_schedulable.
  Qed.

  Theorem tutorial_periodic_edf_schedulable_by_classical_dbf_direct :
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
    1: exact
         (generated_edf_busy_prefix_no_carry_in_bridge_of_backlog_ex
            generated_edf_backlog_free_before_release_ex_proved).
    1: exact periodic_classical_dbf_from_cutoff_ex.
  Qed.
End TutorialClassicalProof.
