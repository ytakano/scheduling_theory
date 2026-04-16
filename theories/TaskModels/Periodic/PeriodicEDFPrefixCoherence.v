From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Semantics.ScheduleLemmas.SchedulePrefix.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Uniprocessor.Generic.FinitePrefixScheduleWitness.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import Uniprocessor.Policies.EDFLemmas.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
Import ListNotations.

Definition periodic_candidates_before
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
  : CandidateSource :=
  fun _ _ _ t =>
    enum_periodic_jobs_before T tasks offset jobs enumT codec (S t).

Lemma periodic_candidates_before_prefix_extensional :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) jobs' m s1 s2 t,
    periodic_candidates_before T tasks offset jobs enumT codec jobs' m s1 t =
    periodic_candidates_before T tasks offset jobs enumT codec jobs' m s2 t.
Proof.
  intros. unfold periodic_candidates_before. reflexivity.
Qed.

Lemma expected_release_ge_index :
  forall T tasks offset τ k,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    k <= expected_release tasks offset τ k.
Proof.
  intros T tasks offset τ k Hwf Hτ.
  unfold expected_release.
  pose proof (Hwf τ Hτ) as Hperiod.
  nia.
Qed.

Lemma filter_all_false :
  forall A (f : A -> bool) l,
    (forall x, In x l -> f x = false) ->
    filter f l = [].
Proof.
  intros A f l Hall.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite (Hall x (or_introl eq_refl)).
    apply IH.
    intros y Hy.
    apply Hall.
    right; exact Hy.
Qed.

Lemma filter_filter :
  forall A (f g : A -> bool) l,
    filter f (filter g l) = filter (fun x => f x && g x) l.
Proof.
  intros A f g l.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - destruct (g x) eqn:Hg; simpl.
    + destruct (f x) eqn:Hf; simpl; rewrite IH; reflexivity.
    + destruct (f x); simpl; exact IH.
Qed.

Lemma before_indices_suffix_empty :
  forall T tasks offset τ t H,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k => Nat.ltb (expected_release tasks offset τ k) (S t))
      (seq (S t) (H - S t)) = [].
Proof.
  intros T tasks offset τ t H Hwf Hτ Hle.
  apply filter_all_false.
  intros k Hin.
  apply in_seq in Hin.
  destruct Hin as [Hk _].
  apply Nat.ltb_ge.
  eapply Nat.le_trans.
  - exact Hk.
  - exact (expected_release_ge_index T tasks offset τ k Hwf Hτ).
Qed.

Lemma before_indices_on_large_horizon :
  forall T tasks offset τ t H,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k => Nat.ltb (expected_release tasks offset τ k) (S t))
      (seq 0 H) =
    enum_periodic_indices_upto tasks offset τ (S t).
Proof.
  intros T tasks offset τ t H Hwf Hτ Hle.
  unfold enum_periodic_indices_upto.
  replace H with (S t + (H - S t)) by lia.
  rewrite seq_app, filter_app.
  replace (0 + S t) with (S t) by lia.
  rewrite (before_indices_suffix_empty T tasks offset τ t H Hwf Hτ Hle).
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma filter_before_indices_upto :
  forall T tasks offset τ t H,
    well_formed_periodic_tasks_on T tasks ->
    T τ ->
    S t <= H ->
    filter
      (fun k => Nat.ltb (expected_release tasks offset τ k) (S t))
      (enum_periodic_indices_upto tasks offset τ H) =
    enum_periodic_indices_upto tasks offset τ (S t).
Proof.
  intros T tasks offset τ t H Hwf Hτ Hle.
  unfold enum_periodic_indices_upto.
  rewrite filter_filter.
  assert (Hfg :
    filter
      (fun x =>
         (expected_release tasks offset τ x <? S t)
         && (expected_release tasks offset τ x <? H))
      (seq 0 H) =
    filter
      (fun x => expected_release tasks offset τ x <? S t)
      (seq 0 H)).
  {
    apply filter_ext_in.
    intros k Hin.
    destruct (Nat.ltb (expected_release tasks offset τ k) (S t)) eqn:Hbefore; simpl.
    - apply Nat.ltb_lt in Hbefore.
      apply Nat.ltb_lt.
      lia.
    - reflexivity.
  }
  rewrite Hfg.
  exact (before_indices_on_large_horizon T tasks offset τ t H Hwf Hτ Hle).
Qed.

Lemma filter_map_periodic_jobs_by_before :
  forall T tasks offset jobs τ H t
         (codec : PeriodicCodec T tasks offset jobs) ks,
    T τ ->
    (forall k, In k ks -> expected_release tasks offset τ k < H) ->
    filter (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (map (global_periodic_job_id_of T tasks offset jobs codec τ) ks) =
    map (global_periodic_job_id_of T tasks offset jobs codec τ)
      (filter (fun k => Nat.ltb (expected_release tasks offset τ k) (S t)) ks).
Proof.
  intros T tasks offset jobs τ H t codec ks Hτ Hks.
  induction ks as [|k ks IH]; simpl.
  - reflexivity.
  - pose proof (Hks k (or_introl eq_refl)) as HkH.
    pose proof
      (global_periodic_job_id_of_sound T tasks offset jobs codec τ k Hτ)
      as [Htask [Hidx Hgen]].
    pose proof (generated_job_release tasks offset jobs _ Hgen) as Hrel.
    rewrite Htask, Hidx in Hrel.
    rewrite Hrel.
    destruct (Nat.ltb (expected_release tasks offset τ k) (S t)) eqn:Hbefore; simpl.
    + f_equal.
      apply IH.
      intros k' Hin.
      apply Hks.
      right; exact Hin.
    + apply IH.
      intros k' Hin.
      apply Hks.
      right; exact Hin.
Qed.

Lemma enum_periodic_jobs_upto_filter_before :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs) t,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, In τ enumT -> T τ) ->
    S t <= H ->
    filter
      (fun j => Nat.ltb (job_release (jobs j)) (S t))
      (enum_periodic_jobs_upto
         T tasks offset jobs H enumT
         (periodic_finite_horizon_codec_of T tasks offset jobs H codec)) =
    enum_periodic_jobs_before T tasks offset jobs enumT codec (S t).
Proof.
  intros T tasks offset jobs H enumT codec t Hwf HenumT_sound Hle.
  induction enumT as [|τ enumT IH]; simpl.
  - reflexivity.
  - rewrite filter_app.
    rewrite
      (filter_map_periodic_jobs_by_before
         T tasks offset jobs τ H t codec
         (enum_periodic_indices_upto tasks offset τ H)
         (HenumT_sound τ (or_introl eq_refl))
         (fun k Hin =>
            proj2
              ((proj1 (in_enum_periodic_indices_upto_iff tasks offset τ H k)) Hin))).
    rewrite filter_before_indices_upto
      with (T := T) (tasks := tasks) (offset := offset) (τ := τ)
           (t := t) (H := H); [|exact Hwf | exact (HenumT_sound τ (or_introl eq_refl)) | exact Hle].
    rewrite IH.
    + reflexivity.
    + intros τ' Hτ'.
      apply HenumT_sound.
      right; exact Hτ'.
Qed.

Lemma future_job_not_eligible_at_time :
  forall T tasks offset jobs H enumT
         (codec : PeriodicCodec T tasks offset jobs) sched t j,
    (forall τ, In τ enumT -> T τ) ->
    In j (enum_periodic_jobs_upto
            T tasks offset jobs H enumT
            (periodic_finite_horizon_codec_of T tasks offset jobs H codec)) ->
    Nat.ltb (job_release (jobs j)) (S t) = false ->
    ~ eligible jobs 1 sched j t.
Proof.
  intros T tasks offset jobs H enumT codec sched t j HenumT_sound Hin Hbefore.
  pose proof
    (enum_periodic_jobs_upto_sound
       T tasks offset jobs H enumT
       (periodic_finite_horizon_codec_of T tasks offset jobs H codec)
       HenumT_sound j Hin) as Hjob.
  apply Nat.ltb_ge in Hbefore.
  intro Helig.
  pose proof (eligible_after_release jobs 1 sched j t Helig) as Hrel.
  lia.
Qed.

Lemma generated_schedule_prefix_coherent_at :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs) H,
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall h t c,
      t < h ->
      h <= H ->
      generated_schedule_prefix
        edf_generic_spec
        (enum_candidates_of
           (enum_periodic_jobs_upto
              T tasks offset jobs H enumT
              (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
        jobs h t c =
      generated_schedule_prefix
        edf_generic_spec
        (periodic_candidates_before T tasks offset jobs enumT codec)
        jobs h t c.
Proof.
  intros T tasks offset jobs enumT codec H Hwf HenumT_complete HenumT_sound h.
  induction h as [|h' IH]; intros t c Hlt Hh.
  - lia.
  - simpl.
    destruct (Nat.eq_dec t h') as [Heq|Hneq].
    + subst t.
      destruct c as [|c'].
      * rewrite Nat.eqb_refl.
        simpl.
        rewrite Nat.ltb_irrefl.
        change
          (choose edf_generic_spec jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
          with
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec))).
        change
          (choose edf_generic_spec jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                (generated_schedule_prefix
                   edf_generic_spec
                   (periodic_candidates_before T tasks offset jobs enumT codec)
                   jobs h') h'))
          with
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                (generated_schedule_prefix
                   edf_generic_spec
                   (periodic_candidates_before T tasks offset jobs enumT codec)
                   jobs h') h')).
        assert (Hagree :
          agrees_before
            (generated_schedule_prefix
               edf_generic_spec
               (enum_candidates_of
                  (enum_periodic_jobs_upto
                     T tasks offset jobs H enumT
                     (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
               jobs h')
            (generated_schedule_prefix
               edf_generic_spec
               (periodic_candidates_before T tasks offset jobs enumT codec)
               jobs h')
            h').
        {
          intros t' c' Hlt'.
          apply IH; try assumption; lia.
        }
        transitivity
          (choose_edf jobs 1
             (generated_schedule_prefix
                edf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs h')
             h'
             (enum_periodic_jobs_upto
                T tasks offset jobs H enumT
                (periodic_finite_horizon_codec_of T tasks offset jobs H codec))).
        2: {
          rewrite choose_edf_filter_ineligible
            with (keep := fun j => Nat.ltb (job_release (jobs j)) (S h')).
          - replace
              (filter (fun j : JobId => job_release (jobs j) <? S h')
                 (enum_periodic_jobs_upto T tasks offset jobs H enumT
                    (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
              with (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                      (generated_schedule_prefix
                         edf_generic_spec
                         (periodic_candidates_before T tasks offset jobs enumT codec)
                         jobs h') h').
            2: {
              rewrite (enum_periodic_jobs_upto_filter_before
                         T tasks offset jobs H enumT codec h'
                         Hwf HenumT_sound).
              2: lia.
              unfold periodic_candidates_before.
              reflexivity.
            }
            unfold periodic_candidates_before.
            reflexivity.
          - intros j Hin Hkeep.
            eapply future_job_not_eligible_at_time; eauto.
        }
        apply choose_edf_agrees_before.
        exact Hagree.
      * rewrite Nat.ltb_irrefl, Nat.eqb_refl.
        simpl.
        destruct (Nat.eqb_spec (S c') 0); [lia | reflexivity].
    + assert (t < h') by lia.
      destruct (Nat.ltb t h') eqn:Hcmp.
      * apply IH; try assumption; lia.
      * apply Nat.ltb_ge in Hcmp.
        lia.
Qed.

Theorem infinite_generated_edf_prefix_coherence :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    forall H,
      agrees_before
        (generated_schedule
           edf_generic_spec
           (enum_candidates_of
              (enum_periodic_jobs_upto
                 T tasks offset jobs H enumT
                 (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
           jobs)
        (generated_schedule
           edf_generic_spec
           (periodic_candidates_before T tasks offset jobs enumT codec)
           jobs)
        H.
Proof.
  intros T tasks offset jobs enumT codec Hwf HenumT_complete HenumT_sound H t c Hlt.
  rewrite <- (generated_schedule_prefix_stable
                edf_generic_spec
                (enum_candidates_of
                   (enum_periodic_jobs_upto
                      T tasks offset jobs H enumT
                      (periodic_finite_horizon_codec_of T tasks offset jobs H codec)))
                jobs H t c Hlt).
  rewrite <- (generated_schedule_prefix_stable
                edf_generic_spec
                (periodic_candidates_before T tasks offset jobs enumT codec)
                jobs H t c Hlt).
  eapply generated_schedule_prefix_coherent_at; eauto; lia.
Qed.

Lemma infinite_generated_edf_scheduler_rel :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    scheduler_rel
      (edf_scheduler (periodic_candidates_before T tasks offset jobs enumT codec))
      jobs 1
      (generated_schedule
         edf_generic_spec
         (periodic_candidates_before T tasks offset jobs enumT codec)
         jobs).
Proof.
  intros T tasks offset jobs enumT codec.
  unfold edf_scheduler, single_cpu_algorithm_schedule.
  simpl.
  split.
  - reflexivity.
  - intros t.
    split.
    + rewrite generated_schedule_eq_cpu0_with_prefix.
      simpl.
      rewrite (choose_edf_agrees_before
                 jobs
                 (generated_schedule_prefix
                    edf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs t)
                 (generated_schedule
                    edf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs)
                 t
                 (periodic_candidates_before T tasks offset jobs enumT codec jobs 1
                    (generated_schedule_prefix
                       edf_generic_spec
                       (periodic_candidates_before T tasks offset jobs enumT codec)
                       jobs t) t)
                 (generated_schedule_prefix_agrees_before
                    edf_generic_spec
                    (periodic_candidates_before T tasks offset jobs enumT codec)
                    jobs t)).
      rewrite
        (periodic_candidates_before_prefix_extensional
           T tasks offset jobs enumT codec jobs 1
           (generated_schedule_prefix
              edf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs t)
           (generated_schedule
              edf_generic_spec
              (periodic_candidates_before T tasks offset jobs enumT codec)
              jobs)
           t).
      reflexivity.
    + intros c Hc.
      apply generated_schedule_other_cpu_idle.
      exact Hc.
Qed.
