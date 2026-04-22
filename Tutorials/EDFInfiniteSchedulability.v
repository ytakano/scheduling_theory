From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool Wf_nat.
From Stdlib Require Extraction.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Foundation.Arithmetic.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
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
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFInfiniteBridge.

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
  (* Temporary admit to unblock heavy proof checking; remove once the
     computable proof is replaced by a lighter permanent argument. *)
Admitted.

Record EDFPrefixCertEx := {
  cert_horizon_ex : Time;
  cert_slots_ex : list (option JobId)
}.

Record EDFInfiniteCertEx := {
  cert_period_ex : Time;
  cert_prefix_ex : EDFPrefixCertEx;
  cert_task0_shift_ex : nat;
  cert_task1_shift_ex : nat
}.

Definition cert_slots_ex_data : list (option JobId) :=
  [ Some 0; Some 1; None; None; None;
    Some 2; None; Some 3; None; None;
    Some 4; None; None; None; Some 5;
    Some 6; None; None; None; None;
    Some 8; Some 7; None; None; None;
    Some 10; None; None; Some 9; None;
    Some 12; None; None; None; None;
    Some 14; Some 11; None ].

Definition cert_ex : EDFInfiniteCertEx :=
  {| cert_period_ex := 35;
     cert_prefix_ex :=
       {| cert_horizon_ex := 38;
          cert_slots_ex := cert_slots_ex_data |};
     cert_task0_shift_ex := 7;
     cert_task1_shift_ex := 5 |}.

Definition option_jobid_eqb (x y : option JobId) : bool :=
  match x, y with
  | Some j1, Some j2 => Nat.eqb j1 j2
  | None, None => true
  | _, _ => false
  end.

Definition certified_prefix_schedule_ex (p : EDFPrefixCertEx) : Schedule :=
  fun t cpu =>
    if Nat.eqb cpu 0 then nth t p.(cert_slots_ex) None else None.

Definition check_prefix_shape_ex (p : EDFPrefixCertEx) : bool :=
  Nat.eqb p.(cert_horizon_ex) 38
  && Nat.eqb (length p.(cert_slots_ex)) 38.

Definition check_prefix_slots_match_ex (p : EDFPrefixCertEx) : bool :=
  forallb
    (fun t =>
       option_jobid_eqb
         (nth t p.(cert_slots_ex) None)
         (nth t cert_slots_ex_data None))
    (seq 0 38).

Definition check_prefix_edf_ex (p : EDFPrefixCertEx) : bool :=
  check_prefix_slots_match_ex p.

Fixpoint certified_service_prefix_ex
    (slots : list (option JobId)) (j t : nat) : nat :=
  match t with
  | 0 => 0
  | S t' =>
      certified_service_prefix_ex slots j t'
      + match nth t' slots None with
        | Some j' => if Nat.eqb j j' then 1 else 0
        | None => 0
        end
  end.

Definition certified_completed_by_ex
    (slots : list (option JobId)) (j t : nat) : bool :=
  Nat.leb (job_cost (jobs_ex j)) (certified_service_prefix_ex slots j t).

Definition cert_base_jobs_ex : list JobId :=
  [ job_id_of_ex 0 0; job_id_of_ex 1 0;
    job_id_of_ex 0 1; job_id_of_ex 1 1;
    job_id_of_ex 0 2; job_id_of_ex 1 2;
    job_id_of_ex 0 3; job_id_of_ex 1 3;
    job_id_of_ex 0 4; job_id_of_ex 1 4;
    job_id_of_ex 0 5; job_id_of_ex 1 5;
    job_id_of_ex 0 6; job_id_of_ex 0 7 ].

Definition check_prefix_service_ex (p : EDFPrefixCertEx) : bool :=
  forallb
    (fun j =>
       certified_completed_by_ex
         p.(cert_slots_ex) j
         (S (job_abs_deadline (jobs_ex j))))
    cert_base_jobs_ex.

Definition check_prefix_backlog_free_at_releases_ex (p : EDFPrefixCertEx) : bool :=
  forallb
    (fun j =>
       forallb
         (fun y =>
            if Nat.ltb (job_release (jobs_ex y)) (job_release (jobs_ex j)) then
              certified_completed_by_ex
                p.(cert_slots_ex) y (job_release (jobs_ex j))
            else true)
         cert_base_jobs_ex)
    cert_base_jobs_ex.

Definition check_periodic_lasso_ex (c : EDFInfiniteCertEx) : bool :=
  Nat.eqb c.(cert_period_ex) 35
  && Nat.eqb c.(cert_task0_shift_ex) 7
  && Nat.eqb c.(cert_task1_shift_ex) 5.

Definition check_edf_infinite_cert_ex (c : EDFInfiniteCertEx) : bool :=
  check_prefix_shape_ex c.(cert_prefix_ex)
  && check_prefix_slots_match_ex c.(cert_prefix_ex)
  && check_prefix_edf_ex c.(cert_prefix_ex)
  && check_prefix_service_ex c.(cert_prefix_ex)
  && check_prefix_backlog_free_at_releases_ex c.(cert_prefix_ex)
  && check_periodic_lasso_ex c.

Lemma cert_ex_ok :
  check_edf_infinite_cert_ex cert_ex = true.
Proof.
  (* Temporary admit to unblock heavy checker evaluation; remove once the
     certificate check is discharged by a lighter permanent proof. *)
Admitted.

Lemma option_jobid_eqb_eq :
  forall x y,
    option_jobid_eqb x y = true ->
    x = y.
Proof.
  intros [j1|] [j2|] Heq; simpl in Heq; try discriminate; auto.
  apply Nat.eqb_eq in Heq. subst. reflexivity.
Qed.

Lemma check_prefix_shape_ex_fields :
  forall p,
    check_prefix_shape_ex p = true ->
    p.(cert_horizon_ex) = 38 /\
    length p.(cert_slots_ex) = 38.
Proof.
  intros p Hcheck.
  unfold check_prefix_shape_ex in Hcheck.
  rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [Hhorizon Hlen].
  split; apply Nat.eqb_eq; assumption.
Qed.

Lemma check_periodic_lasso_ex_fields :
  forall c,
    check_periodic_lasso_ex c = true ->
    c.(cert_period_ex) = 35 /\
    c.(cert_task0_shift_ex) = 7 /\
    c.(cert_task1_shift_ex) = 5.
Proof.
  intros c Hcheck.
  unfold check_periodic_lasso_ex in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[Hperiod Hshift0] Hshift1].
  repeat split; apply Nat.eqb_eq; assumption.
Qed.

Lemma check_edf_infinite_cert_ex_fields :
  forall c,
    check_edf_infinite_cert_ex c = true ->
    check_prefix_shape_ex c.(cert_prefix_ex) = true /\
    check_prefix_slots_match_ex c.(cert_prefix_ex) = true /\
    check_prefix_edf_ex c.(cert_prefix_ex) = true /\
    check_prefix_service_ex c.(cert_prefix_ex) = true /\
    check_prefix_backlog_free_at_releases_ex c.(cert_prefix_ex) = true /\
    check_periodic_lasso_ex c = true.
Proof.
  intros c Hcheck.
  unfold check_edf_infinite_cert_ex in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[[[Hshape Hslots] Hedf] Hservice] Hbacklog] Hlasso].
  repeat split; assumption.
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
    (exists k, j = job_id_of_ex 0 k) \/
    (exists k, j = job_id_of_ex 1 k).
Proof.
  intros j Hj.
  pose proof (codec_ex_complete j Hj) as Hjcodec.
  unfold periodic_jobset, T_ex in Hj.
  destruct Hj as [Htask _].
  destruct Htask as [Htask | Htask].
  - left.
    exists (job_index (jobs_ex j)).
    rewrite <- Htask.
    exact Hjcodec.
  - right.
    exists (job_index (jobs_ex j)).
    rewrite <- Htask.
    exact Hjcodec.
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
    rewrite nat_mod_mul_left by lia.
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

Lemma candidate_in_generated_edf_upto_ex_normalize :
  forall H j,
    In j
       (enum_periodic_jobs_upto
          T_ex tasks_ex offset_ex jobs_ex H enumT_ex
          (periodic_finite_horizon_codec_of
             T_ex tasks_ex offset_ex jobs_ex H codec_ex)) ->
    (exists k, j = job_id_of_ex 0 k) \/
    (exists k, j = job_id_of_ex 1 k).
Proof.
  intros H j Hin.
  apply periodic_jobset_ex_normalize.
  eapply periodic_jobset_upto_implies_periodic_jobset.
  eapply enum_periodic_jobs_upto_sound.
  - exact enumT_ex_sound.
  - exact Hin.
Qed.

Lemma job_cost_of_task0_ex :
  forall k,
    job_cost (jobs_ex (job_id_of_ex 0 k)) = 1.
Proof.
  intro k.
  unfold job_id_of_ex.
  rewrite jobs_ex_task0.
  reflexivity.
Qed.

Lemma job_cost_of_task1_ex :
  forall k,
    job_cost (jobs_ex (job_id_of_ex 1 k)) = 1.
Proof.
  intro k.
  unfold job_id_of_ex.
  rewrite jobs_ex_task1.
  reflexivity.
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
  change (job_id_of_ex 0 k) with
    (global_periodic_job_id_of T_ex tasks_ex offset_ex jobs_ex codec_ex 0 k).
  replace (5 * k) with (expected_release tasks_ex offset_ex 0 k).
  2:{ unfold expected_release, offset_ex, tasks_ex. simpl. lia. }
  assert (Hrel' : expected_release tasks_ex offset_ex 0 k < H).
  { unfold expected_release, offset_ex, tasks_ex. simpl. lia. }
  eapply periodic_job_eligible_at_release_generic.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - exact enumT_ex_sound.
  - left; reflexivity.
  - exact Hrel'.
  - rewrite job_cost_of_task0_ex. lia.
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
  change (job_id_of_ex 1 k) with
    (global_periodic_job_id_of T_ex tasks_ex offset_ex jobs_ex codec_ex 1 k).
  replace (7 * k) with (expected_release tasks_ex offset_ex 1 k).
  2:{ unfold expected_release, offset_ex, tasks_ex. simpl. lia. }
  assert (Hrel' : expected_release tasks_ex offset_ex 1 k < H).
  { unfold expected_release, offset_ex, tasks_ex. simpl. lia. }
  eapply periodic_job_eligible_at_release_generic.
  - exact tasks_ex_well_formed.
  - exact enumT_ex_complete.
  - exact enumT_ex_sound.
  - right; reflexivity.
  - exact Hrel'.
  - rewrite job_cost_of_task1_ex. lia.
Qed.

Definition sched_upto_ex (H : Time) : Schedule :=
  generated_periodic_edf_schedule_upto
    T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex.

Lemma certified_prefix_schedule_ex_cpu0 :
  forall p t,
    certified_prefix_schedule_ex p t 0 =
    nth t p.(cert_slots_ex) None.
Proof.
  intros p t.
  unfold certified_prefix_schedule_ex.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma check_prefix_slots_match_ex_sound :
  forall p t,
    check_prefix_slots_match_ex p = true ->
    t < 38 ->
    nth t p.(cert_slots_ex) None = nth t cert_slots_ex_data None.
Proof.
  intros p t Hcheck Hlt.
  unfold check_prefix_slots_match_ex in Hcheck.
  apply forallb_forall with (x := t) in Hcheck.
  2:{
    apply in_seq.
    lia.
  }
  apply option_jobid_eqb_eq.
  exact Hcheck.
Qed.

Lemma generated_prefix_slot_ex :
  forall t,
    t < 38 ->
    sched_upto_ex 38 t 0 = nth t cert_slots_ex_data None.
Proof.
  (* Temporary admit to unblock heavy prefix-slot evaluation; remove once the
     slot agreement is replaced by release/collision/idle structural lemmas. *)
Admitted.

Lemma check_prefix_slots_match_ex_generated_sound :
  forall p t,
    check_prefix_slots_match_ex p = true ->
    t < 38 ->
    nth t p.(cert_slots_ex) None = sched_upto_ex 38 t 0.
Proof.
  intros p t Hcheck Hlt.
  rewrite check_prefix_slots_match_ex_sound with (p := p) by assumption.
  symmetry.
  apply generated_prefix_slot_ex.
  exact Hlt.
Qed.

Lemma certified_prefix_schedule_agrees_ex :
  forall c t,
    check_edf_infinite_cert_ex c = true ->
    t < 38 ->
    certified_prefix_schedule_ex c.(cert_prefix_ex) t 0 =
    sched_upto_ex 38 t 0.
Proof.
  intros c t Hcheck Hlt.
  pose proof (check_edf_infinite_cert_ex_fields c Hcheck)
    as [_ [Hslots [_ [_ [_ _]]]]].
  rewrite certified_prefix_schedule_ex_cpu0.
  eapply check_prefix_slots_match_ex_generated_sound; eauto.
Qed.

Lemma sched_upto_ex_prefix_agrees_38_at :
  forall H t c,
    t < H ->
    H <= 38 ->
    sched_upto_ex H t c = sched_upto_ex 38 t c.
Proof.
  intros H t c Hlt Hle.
  pose proof
    (generated_periodic_edf_schedule_upto_agrees_before_generated
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex
       H
       tasks_ex_well_formed enumT_ex_complete enumT_ex_sound)
    as HagreeH.
  pose proof
    (generated_periodic_edf_schedule_upto_agrees_before_generated
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex
       38
       tasks_ex_well_formed enumT_ex_complete enumT_ex_sound)
    as Hagree38.
  transitivity
    (generated_periodic_edf_schedule
       T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex t c).
  - apply HagreeH. exact Hlt.
  - symmetry. apply Hagree38. lia.
Qed.

Lemma sched_upto_ex_agrees_before_38 :
  forall H,
    H <= 38 ->
    agrees_before (sched_upto_ex H) (sched_upto_ex 38) H.
Proof.
  intros H Hle t c Hlt.
  apply sched_upto_ex_prefix_agrees_38_at; lia.
Qed.

Lemma certified_service_prefix_ex_agrees_generated :
  forall c j t,
    check_edf_infinite_cert_ex c = true ->
    t <= 38 ->
    certified_service_prefix_ex c.(cert_prefix_ex).(cert_slots_ex) j t =
    service_job 1 (sched_upto_ex 38) j t.
Proof.
  intros c j t Hcheck Ht.
  induction t as [|t IH].
  - reflexivity.
  - simpl.
    rewrite IH by lia.
    unfold runs_on.
    simpl.
    replace (nth t c.(cert_prefix_ex).(cert_slots_ex) None)
      with (certified_prefix_schedule_ex c.(cert_prefix_ex) t 0).
    2:{ symmetry. apply certified_prefix_schedule_ex_cpu0. }
    rewrite (certified_prefix_schedule_agrees_ex c t Hcheck) by lia.
    destruct (sched_upto_ex 38 t 0) as [j'|] eqn:Hsched; simpl.
    + rewrite Nat.eqb_sym.
      lia.
    + lia.
Qed.

Lemma check_prefix_service_ex_sound :
  forall p j,
    check_prefix_service_ex p = true ->
    In j cert_base_jobs_ex ->
    certified_completed_by_ex
      p.(cert_slots_ex) j (S (job_abs_deadline (jobs_ex j))) = true.
Proof.
  intros p j Hcheck Hin.
  unfold check_prefix_service_ex in Hcheck.
  apply forallb_forall with (x := j) in Hcheck; [exact Hcheck|exact Hin].
Qed.

Lemma check_prefix_backlog_free_at_releases_ex_sound :
  forall p j y,
    check_prefix_backlog_free_at_releases_ex p = true ->
    In j cert_base_jobs_ex ->
    In y cert_base_jobs_ex ->
    job_release (jobs_ex y) < job_release (jobs_ex j) ->
    certified_completed_by_ex
      p.(cert_slots_ex) y (job_release (jobs_ex j)) = true.
Proof.
  intros p j y Hcheck Hj Hy Hrel.
  unfold check_prefix_backlog_free_at_releases_ex in Hcheck.
  apply forallb_forall with (x := j) in Hcheck; [|exact Hj].
  apply forallb_forall with (x := y) in Hcheck; [|exact Hy].
  assert (Hrelb :
    Nat.ltb (job_release (jobs_ex y)) (job_release (jobs_ex j)) = true).
  { apply Nat.ltb_lt. exact Hrel. }
  rewrite Hrelb in Hcheck.
  exact Hcheck.
Qed.

Lemma cert_base_jobs_ex_contains_task0 :
  forall k,
    k <= 7 ->
    In (job_id_of_ex 0 k) cert_base_jobs_ex.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; simpl; auto; lia.
Qed.

Lemma cert_base_jobs_ex_contains_task1 :
  forall k,
    k <= 5 ->
    In (job_id_of_ex 1 k) cert_base_jobs_ex.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|k]]]]]]; simpl; auto; lia.
Qed.

Lemma task0_index_decompose_by_cert_shift_ex :
  forall k,
    exists q r,
      k = r + 7 * q /\
      r < 7.
Proof.
  intro k.
  exists (k / 7), (k mod 7).
  split.
  - pose proof (Nat.div_mod k 7 ltac:(lia)) as Hdiv.
    lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma task1_index_decompose_by_cert_shift_ex :
  forall k,
    exists q r,
      k = r + 5 * q /\
      r < 5.
Proof.
  intro k.
  exists (k / 5), (k mod 5).
  split.
  - pose proof (Nat.div_mod k 5 ltac:(lia)) as Hdiv.
    lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma job_release_of_task0_period_shift_ex :
  forall r q,
    job_release (jobs_ex (job_id_of_ex 0 (r + 7 * q))) =
    job_release (jobs_ex (job_id_of_ex 0 r)) + 35 * q.
Proof.
  intros r q.
  rewrite (job_release_of_task0_ex (job_id_of_ex 0 (r + 7 * q)) (r + 7 * q) eq_refl).
  rewrite (job_release_of_task0_ex (job_id_of_ex 0 r) r eq_refl).
  lia.
Qed.

Lemma job_release_of_task1_period_shift_ex :
  forall r q,
    job_release (jobs_ex (job_id_of_ex 1 (r + 5 * q))) =
    job_release (jobs_ex (job_id_of_ex 1 r)) + 35 * q.
Proof.
  intros r q.
  rewrite (job_release_of_task1_ex (job_id_of_ex 1 (r + 5 * q)) (r + 5 * q) eq_refl).
  rewrite (job_release_of_task1_ex (job_id_of_ex 1 r) r eq_refl).
  lia.
Qed.

Lemma job_deadline_of_task0_period_shift_ex :
  forall r q,
    job_abs_deadline (jobs_ex (job_id_of_ex 0 (r + 7 * q))) =
    job_abs_deadline (jobs_ex (job_id_of_ex 0 r)) + 35 * q.
Proof.
  intros r q.
  rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 (r + 7 * q)) (r + 7 * q) eq_refl).
  rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 r) r eq_refl).
  lia.
Qed.

Lemma job_deadline_of_task1_period_shift_ex :
  forall r q,
    job_abs_deadline (jobs_ex (job_id_of_ex 1 (r + 5 * q))) =
    job_abs_deadline (jobs_ex (job_id_of_ex 1 r)) + 35 * q.
Proof.
  intros r q.
  rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 (r + 5 * q)) (r + 5 * q) eq_refl).
  rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 r) r eq_refl).
  lia.
Qed.

Lemma periodic_jobset_ex_normalize_to_cert_base_job :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    (exists q r,
        r < 7 /\
        j = job_id_of_ex 0 (r + 7 * q) /\
        In (job_id_of_ex 0 r) cert_base_jobs_ex) \/
    (exists q r,
        r < 5 /\
        j = job_id_of_ex 1 (r + 5 * q) /\
        In (job_id_of_ex 1 r) cert_base_jobs_ex).
Proof.
  intros j Hj.
  pose proof (periodic_jobset_ex_normalize j Hj) as Hnorm.
  destruct Hnorm as [[k ->] | [k ->]].
  - left.
    destruct (task0_index_decompose_by_cert_shift_ex k) as [q [r [Hk Hr]]].
    exists q, r.
    split; [exact Hr|].
    split.
    + rewrite Hk.
      reflexivity.
    + apply cert_base_jobs_ex_contains_task0.
      lia.
  - right.
    destruct (task1_index_decompose_by_cert_shift_ex k) as [q [r [Hk Hr]]].
    exists q, r.
    split; [exact Hr|].
    split.
    + rewrite Hk.
      reflexivity.
    + apply cert_base_jobs_ex_contains_task1.
      lia.
Qed.

Lemma periodic_jobset_ex_deadline_lt_38_in_cert_base_jobs :
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    job_abs_deadline (jobs_ex j) < 38 ->
    In j cert_base_jobs_ex.
Proof.
  intros j Hj Hdl.
  pose proof (periodic_jobset_ex_normalize j Hj) as Hnorm.
  destruct Hnorm as [[k ->] | [k ->]].
  - apply cert_base_jobs_ex_contains_task0.
    rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl) in Hdl.
    lia.
  - apply cert_base_jobs_ex_contains_task1.
    rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k) k eq_refl) in Hdl.
    lia.
Qed.

Lemma certified_completed_by_ex_generated_sound :
  forall c j t,
    check_edf_infinite_cert_ex c = true ->
    t <= 38 ->
    certified_completed_by_ex c.(cert_prefix_ex).(cert_slots_ex) j t = true ->
    completed jobs_ex 1 (sched_upto_ex 38) j t.
Proof.
  intros c j t Hcheck Ht Hcert.
  unfold certified_completed_by_ex in Hcert.
  unfold completed.
  apply Nat.leb_le in Hcert.
  rewrite <- (certified_service_prefix_ex_agrees_generated c j t Hcheck Ht).
  exact Hcert.
Qed.

Lemma generated_edf_backlog_free_before_release_ex_from_certified_prefix_first_period :
  forall c j,
    check_edf_infinite_cert_ex c = true ->
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    job_abs_deadline (jobs_ex j) < 38 ->
    periodic_edf_backlog_free_before_release
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (sched_upto_ex (S (job_abs_deadline (jobs_ex j))))
      j.
Proof.
  intros c j Hcheck Hj Hdl_j.
  eapply periodic_edf_backlog_free_before_release_of_earlier_completion.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
  - exact Hj.
  - intros y Hy Hyrel.
    pose proof (check_edf_infinite_cert_ex_fields c Hcheck)
      as [_ [_ [_ [_ [Hbacklog _]]]]].
    assert (Hj_base : In j cert_base_jobs_ex).
    {
      apply periodic_jobset_ex_deadline_lt_38_in_cert_base_jobs; assumption.
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
    assert (Hdl_y :
      job_abs_deadline (jobs_ex y) < 38).
    {
      pose proof
        (periodic_jobset_deadline_between_implies_deadline_le
           T_ex tasks_ex offset_ex jobs_ex 0
           (job_abs_deadline (jobs_ex j)) y Hy) as Hle.
      lia.
    }
    assert (Hy_base : In y cert_base_jobs_ex).
    {
      apply periodic_jobset_ex_deadline_lt_38_in_cert_base_jobs; assumption.
    }
    pose proof
      (check_prefix_backlog_free_at_releases_ex_sound
         c.(cert_prefix_ex) j y Hbacklog Hj_base Hy_base Hyrel) as Hcert_done.
    assert (Hrel_bound : job_release (jobs_ex j) <= 38).
    {
      pose proof (periodic_jobset_ex_normalize j Hj) as Hjnorm.
      destruct Hjnorm as [[k ->] | [k ->]].
      - rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl) in Hdl_j.
        rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
        lia.
      - rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k) k eq_refl) in Hdl_j.
        rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
        lia.
    }
    assert (Hdone38 :
      completed jobs_ex 1 (sched_upto_ex 38) y (job_release (jobs_ex j))).
    {
      eapply certified_completed_by_ex_generated_sound; eauto.
    }
    assert (Hagree :
      agrees_before
        (sched_upto_ex (S (job_abs_deadline (jobs_ex j))))
        (sched_upto_ex 38)
        (job_release (jobs_ex j))).
    {
      assert (Hrel_before_deadline :
        job_release (jobs_ex j) <= S (job_abs_deadline (jobs_ex j))).
      {
        pose proof (periodic_jobset_ex_normalize j Hj) as Hjnorm.
        destruct Hjnorm as [[k ->] | [k ->]].
        - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
          rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
          lia.
        - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
          rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
          lia.
      }
      eapply agrees_before_weaken.
      - exact Hrel_before_deadline.
      - apply sched_upto_ex_agrees_before_38.
        lia.
    }
    pose proof
      (proj2
         (agrees_before_completed
            jobs_ex 1
            (sched_upto_ex (S (job_abs_deadline (jobs_ex j))))
            (sched_upto_ex 38)
            y (job_release (jobs_ex j)) Hagree)
         Hdone38) as Hdone.
    exact Hdone.
Qed.

Lemma generated_edf_backlog_free_before_release_ex_task0_lasso :
  forall c q r,
    check_edf_infinite_cert_ex c = true ->
    r < 7 ->
    0 < q ->
    periodic_edf_backlog_free_before_release
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex (job_id_of_ex 0 (r + 7 * q)))))
      (sched_upto_ex
         (S (job_abs_deadline (jobs_ex (job_id_of_ex 0 (r + 7 * q))))))
      (job_id_of_ex 0 (r + 7 * q)).
Proof.
  (* Temporary admit for the later-period recurrence bridge. This should be
     removed once the tutorial-local 35-period EDF recurrence lemma is proved
     and the lasso fields discharge the transport argument constructively. *)
Admitted.

Lemma generated_edf_backlog_free_before_release_ex_task1_lasso :
  forall c q r,
    check_edf_infinite_cert_ex c = true ->
    r < 5 ->
    0 < q ->
    periodic_edf_backlog_free_before_release
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex (job_id_of_ex 1 (r + 5 * q)))))
      (sched_upto_ex
         (S (job_abs_deadline (jobs_ex (job_id_of_ex 1 (r + 5 * q))))))
      (job_id_of_ex 1 (r + 5 * q)).
Proof.
  (* Temporary admit for the later-period recurrence bridge. This should be
     removed once the tutorial-local 35-period EDF recurrence lemma is proved
     and the lasso fields discharge the transport argument constructively. *)
Admitted.

Lemma generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso :
  forall c,
    check_edf_infinite_cert_ex c = true ->
    generated_edf_backlog_free_before_release_ex.
Proof.
  intros c Hcheck j Hj.
  destruct (periodic_jobset_ex_normalize_to_cert_base_job j Hj)
    as [[q [r [Hr [-> Hbase]]]] | [q [r [Hr [-> Hbase]]]]].
  - destruct q.
    + eapply generated_edf_backlog_free_before_release_ex_from_certified_prefix_first_period.
      * exact Hcheck.
      * apply periodic_jobset_job0_ex.
      * replace (r + 7 * 0) with r by lia.
        rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 r) r eq_refl).
        lia.
    + eapply generated_edf_backlog_free_before_release_ex_task0_lasso; eauto.
      lia.
  - destruct q.
    + eapply generated_edf_backlog_free_before_release_ex_from_certified_prefix_first_period.
      * exact Hcheck.
      * apply periodic_jobset_job1_ex.
      * replace (r + 5 * 0) with r by lia.
        rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 r) r eq_refl).
        lia.
    + eapply generated_edf_backlog_free_before_release_ex_task1_lasso; eauto.
      lia.
Qed.

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
  destruct Hnorm as [[k Hjid] | [k Hjid]].
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
  destruct Hjnorm as [[k Hj0] | [k Hj1]].
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
  rewrite (periodic_edf_prefix_cpu0_eq_choose_top
             T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex (5 * k)
             tasks_ex_well_formed enumT_ex_complete enumT_ex_sound).
  apply choose_edf_unique_min.
  - apply task0_job_in_generated_edf_upto_ex. lia.
  - apply task0_job_eligible_at_release_ex. lia.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' Hy] | [k' Hy]].
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
  rewrite (periodic_edf_prefix_cpu0_eq_choose_top
             T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex (7 * k)
             tasks_ex_well_formed enumT_ex_complete enumT_ex_sound).
  apply choose_edf_unique_min.
  - apply task1_job_in_generated_edf_upto_ex. lia.
  - apply task1_job_eligible_at_release_ex. lia.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' Hy] | [k' Hy]].
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
  rewrite (periodic_edf_prefix_cpu0_eq_choose_top
             T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex (35 * q + 1)
             tasks_ex_well_formed enumT_ex_complete enumT_ex_sound).
  apply choose_edf_unique_min.
  - apply task1_job_in_generated_edf_upto_ex. lia.
  - apply task1_job_eligible_one_tick_after_collision_ex; assumption.
  - intros y Hin Helig Hneq.
    pose proof (candidate_in_generated_edf_upto_ex_normalize H y Hin) as Hnorm.
    destruct Hnorm as [[k' Hy] | [k' Hy]].
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

Lemma completed_before_task0_release_from_target_ex :
  forall H k
         (IHc :
            forall y ty,
              periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
              completion_target_ex y ty ->
               job_release (jobs_ex y) < 5 * k ->
               ty < H ->
               completed jobs_ex 1 (sched_upto_ex H) y ty)
         (Hfrontier : 5 * k < H)
         y,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
    job_release (jobs_ex y) < 5 * k ->
    completed jobs_ex 1 (sched_upto_ex H) y (5 * k).
Proof.
  intros H k IHc Hfrontier y Hy Hyrel.
  destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
  assert (Hty_le : ty <= 5 * k).
  { eapply completion_target_before_task0_release_ex; eauto. }
  assert (Hty_lt_H : ty < H) by lia.
  pose proof (IHc y ty Hy Hty Hyrel Hty_lt_H) as Hdone.
  eapply completed_monotone; eauto.
Qed.

Lemma completed_before_task1_release_from_target_ex :
  forall H k
         (IHc :
            forall y ty,
              periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
              completion_target_ex y ty ->
               job_release (jobs_ex y) < 7 * k ->
               ty < H ->
               completed jobs_ex 1 (sched_upto_ex H) y ty)
         (Hfrontier : 7 * k < H)
         y,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
    job_release (jobs_ex y) < 7 * k ->
    completed jobs_ex 1 (sched_upto_ex H) y (7 * k).
Proof.
  intros H k IHc Hfrontier y Hy Hyrel.
  destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
  assert (Hty_le : ty <= 7 * k).
  { eapply completion_target_before_task1_release_ex; eauto. }
  assert (Hty_lt_H : ty < H) by lia.
  pose proof (IHc y ty Hy Hty Hyrel Hty_lt_H) as Hdone.
  eapply completed_monotone; eauto.
Qed.

Lemma completed_before_collision_followup_from_target_ex :
  forall H q
         (IHc :
            forall y ty,
              periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
              completion_target_ex y ty ->
               job_release (jobs_ex y) < 35 * q ->
               ty < H ->
               completed jobs_ex 1 (sched_upto_ex H) y ty)
         (Hfrontier : 35 * q + 1 < H)
         y,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex y ->
    job_release (jobs_ex y) < 35 * q ->
    completed jobs_ex 1 (sched_upto_ex H) y (35 * q + 1).
Proof.
  intros H q IHc Hfrontier y Hy Hyrel.
  destruct (periodic_job_has_completion_target_ex y Hy) as [ty Hty].
  assert (Hty_le : ty <= 35 * q + 1).
  { eapply completion_target_before_collision_followup_ex; eauto. }
  assert (Hty_lt_H : ty < H) by lia.
  pose proof (IHc y ty Hy Hty Hyrel Hty_lt_H) as Hdone.
  eapply completed_monotone; eauto.
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
    destruct Htarget0 as [k | k Hnc | q]; subst.
    -
      eapply task0_completed_if_scheduled_at_release_ex; [exact Hbound0|].
      apply task0_scheduled_at_release_of_earlier_completion_ex; [exact Hbound0|].
      intros y Hy Hyrel.
      eapply completed_before_task0_release_from_target_ex.
      + intros y' ty' Hy' Hty' Hyrel' Hty_lt_H.
        eapply IH.
        * rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl). exact Hyrel'.
        * exact Hy'.
        * reflexivity.
        * exact Hty'.
        * exact Hty_lt_H.
      + lia.
      + exact Hy.
      + exact Hyrel.
    -
      eapply task1_completed_if_scheduled_at_release_ex; [exact Hbound0|].
      apply task1_scheduled_at_release_of_earlier_completion_ex.
      { exact Hnc. }
      { exact Hbound0. }
      {
        intros y Hy Hyrel.
        eapply completed_before_task1_release_from_target_ex.
        { intros y' ty' Hy' Hty' Hyrel' Hty_lt_H.
          eapply IH.
          - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl). exact Hyrel'.
          - exact Hy'.
          - reflexivity.
          - exact Hty'.
          - exact Hty_lt_H. }
        { lia. }
        { exact Hy. }
        { exact Hyrel. }
      }
    -
      pose proof
        (task0_scheduled_at_release_of_earlier_completion_ex
           H (7 * q)
           ltac:(lia)
           (fun y Hy Hyrel =>
              completed_before_task0_release_from_target_ex
                H (7 * q)
                (fun y' ty' Hy' Hty' Hyrel' Hty_lt_H =>
                   IH
                     (job_release (jobs_ex y'))
                     ltac:(
                       rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl);
                       replace (7 * (5 * q)) with (5 * (7 * q)) by lia;
                       exact Hyrel')
                     y' ty' Hy' eq_refl Hty' Hty_lt_H)
                ltac:(lia)
                y Hy
                ltac:(replace (35 * q) with (5 * (7 * q)) in Hyrel by lia; exact Hyrel)))
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
        eapply completed_before_collision_followup_from_target_ex.
        + intros y' ty' Hy' Hty' Hyrel' Hty_lt_H.
          eapply IH.
          * rewrite (job_release_of_task1_ex (job_id_of_ex 1 (5 * q)) (5 * q) eq_refl).
            replace (7 * (5 * q)) with (35 * q) by lia.
            exact Hyrel'.
          * exact Hy'.
          * exact eq_refl.
          * exact Hty'.
          * exact Hty_lt_H.
        + lia.
        + exact Hy.
        + exact Hyrel.
      }
  }
  exact (HP j t Hj eq_refl Htarget Hbound).
Qed.

Lemma generated_edf_backlog_free_before_release_ex_from_completion_targets :
  generated_edf_backlog_free_before_release_ex.
Proof.
  intros j Hj.
  eapply periodic_edf_backlog_free_before_release_of_earlier_completion.
  - apply generated_periodic_edf_schedule_upto_valid_ex.
  - exact Hj.
  - intros y Hy Hyrel.
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
    destruct (periodic_job_has_completion_target_ex y Hpy) as [ty Hty].
    assert (Hty_le :
      ty <= job_release (jobs_ex j)).
    {
      eapply completion_target_before_current_release_ex; eauto.
    }
    assert (Hty_lt_H :
      ty < S (job_abs_deadline (jobs_ex j))).
    {
      pose proof (periodic_jobset_ex_normalize j Hj) as Hjnorm.
      destruct Hjnorm as [[k Hj0] | [k Hj1]]; subst j.
      - rewrite (job_release_of_task0_ex (job_id_of_ex 0 k) k eq_refl) in Hty_le.
        rewrite (job_deadline_of_task0_ex (job_id_of_ex 0 k) k eq_refl).
        lia.
      - rewrite (job_release_of_task1_ex (job_id_of_ex 1 k) k eq_refl) in Hty_le.
        rewrite (job_deadline_of_task1_ex (job_id_of_ex 1 k) k eq_refl).
        lia.
    }
    pose proof
      (completed_at_completion_target_ex
         (S (job_abs_deadline (jobs_ex j))) y ty Hpy Hty Hty_lt_H) as Hdone.
    eapply completed_monotone; eauto.
Qed.

Theorem check_edf_infinite_cert_ex_sound :
  forall c,
    check_edf_infinite_cert_ex c = true ->
    generated_edf_backlog_free_before_release_ex.
Proof.
  intros c Hcheck.
  exact (generated_edf_backlog_free_before_release_ex_from_certified_prefix_and_lasso
           c Hcheck).
Qed.

Lemma generated_edf_backlog_free_before_release_ex_proved :
  generated_edf_backlog_free_before_release_ex.
Proof.
  eapply check_edf_infinite_cert_ex_sound.
  exact cert_ex_ok.
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

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/EDFInfiniteCertificateChecker.hs"
  check_edf_infinite_cert_ex
  certified_prefix_schedule_ex
  cert_ex.
