From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Common.FiniteHorizonWitness.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicInfiniteJobset.
From RocqSched Require Import TaskModels.Jitter.JitteredPeriodicCodec.
Import ListNotations.

Definition JitteredPeriodicFiniteHorizonWitness
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type :=
  FiniteHorizonWitness
    (jittered_periodic_jobset_upto T tasks offset jitter jobs H).

Definition enum_jittered_periodic_indices_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : list nat :=
  filter
    (fun k => Nat.ltb (expected_release tasks offset τ k) H)
    (seq 0 H).

Lemma in_enum_jittered_periodic_indices_upto_iff :
  forall tasks offset τ H k,
    In k (enum_jittered_periodic_indices_upto tasks offset τ H) <->
    k < H /\ expected_release tasks offset τ k < H.
Proof.
  intros tasks offset τ H k.
  unfold enum_jittered_periodic_indices_upto.
  rewrite filter_In.
  rewrite in_seq.
  rewrite Nat.ltb_lt.
  split.
  - intros [[_ Hk] Hrel]. split; [exact Hk | exact Hrel].
  - intros [Hk Hrel]. split; [split; [lia | exact Hk] | exact Hrel].
Qed.

Definition enum_jittered_periodic_jobs_upto_unfiltered
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : JitteredPeriodicFiniteHorizonCodec
               T tasks offset jitter jobs H)
    : list JobId :=
  let id_of :=
    jittered_periodic_job_id_of T tasks offset jitter jobs H codec in
  flat_map
    (fun τ => map (id_of τ) (enum_jittered_periodic_indices_upto tasks offset τ H))
    enumT.

Definition enum_jittered_periodic_jobs_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : JitteredPeriodicFiniteHorizonCodec
               T tasks offset jitter jobs H)
    : list JobId :=
  filter
    (fun j => Nat.ltb (job_release (jobs j)) H)
    (enum_jittered_periodic_jobs_upto_unfiltered
       T tasks offset jitter jobs H enumT codec).

Lemma enum_jittered_periodic_jobs_upto_sound :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    (forall τ, In τ enumT -> T τ) ->
    forall j,
      In j (enum_jittered_periodic_jobs_upto
              T tasks offset jitter jobs H enumT codec) ->
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j.
Proof.
  intros T tasks offset jitter jobs H enumT codec HenumT_sound j Hj.
  unfold enum_jittered_periodic_jobs_upto in Hj.
  apply filter_In in Hj.
  destruct Hj as [Hjunfiltered Hrelease].
  apply Nat.ltb_lt in Hrelease.
  unfold enum_jittered_periodic_jobs_upto_unfiltered in Hjunfiltered.
  apply in_flat_map in Hjunfiltered.
  destruct Hjunfiltered as [τ [HτinT Hjinmap]].
  apply in_map_iff in Hjinmap.
  destruct Hjinmap as [k [Hjk Hkin]].
  apply in_enum_jittered_periodic_indices_upto_iff in Hkin.
  destruct Hkin as [_ Hexpected].
  subst j.
  pose proof (HenumT_sound τ HτinT) as HT.
  pose proof
    (jittered_periodic_job_id_of_sound
       T tasks offset jitter jobs H codec τ k HT Hexpected)
    as [Htask [Hidx Hgen]].
  split.
  - rewrite Htask. exact HT.
  - split.
    + exact Hgen.
    + exact Hrelease.
Qed.

Lemma enum_jittered_periodic_jobs_upto_complete :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    forall j,
      jittered_periodic_jobset_upto T tasks offset jitter jobs H j ->
      In j (enum_jittered_periodic_jobs_upto
              T tasks offset jitter jobs H enumT codec).
Proof.
  intros T tasks offset jitter jobs H enumT codec Hwf HenumT_complete j Hjobset.
  pose proof
    (jittered_periodic_jobset_upto_implies_task_in_scope
       T tasks offset jitter jobs H j Hjobset) as HT.
  pose proof (HenumT_complete _ HT) as HτinT.
  pose proof
    (jittered_periodic_jobset_upto_implies_index_lt
       T tasks offset jitter jobs H j Hwf Hjobset) as Hk_lt.
  pose proof
    (jittered_periodic_jobset_upto_expected_release_lt
       T tasks offset jitter jobs H j Hjobset) as Hexpected_lt.
  pose proof
    (jittered_periodic_job_id_of_complete
       T tasks offset jitter jobs H codec j Hjobset) as Hjcodec.
  unfold enum_jittered_periodic_jobs_upto.
  apply filter_In.
  split.
  - unfold enum_jittered_periodic_jobs_upto_unfiltered.
    apply in_flat_map.
    exists (job_task (jobs j)).
    split.
    + exact HτinT.
    + apply in_map_iff.
      exists (job_index (jobs j)).
      split.
      * symmetry. exact Hjcodec.
      * apply in_enum_jittered_periodic_indices_upto_iff.
        split; [exact Hk_lt | exact Hexpected_lt].
  - apply Nat.ltb_lt.
    exact
      (jittered_periodic_jobset_upto_implies_release_lt
         T tasks offset jitter jobs H j Hjobset).
Qed.

Lemma enum_jittered_periodic_jobs_upto_task_index_nodup_for_task :
  forall T tasks offset jitter jobs H τ ks
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    T τ ->
    (forall k, In k ks -> expected_release tasks offset τ k < H) ->
    NoDup ks ->
    NoDup
      (map (fun j => (job_task (jobs j), job_index (jobs j)))
           (map (jittered_periodic_job_id_of
                   T tasks offset jitter jobs H codec τ) ks)).
Proof.
  intros T tasks offset jitter jobs H τ ks codec HT Hrel.
  induction 1 as [|k ks Hnin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [j' [Heq Hinj']].
      apply in_map_iff in Hinj'.
      destruct Hinj' as [k' [Hj'_eq Hin']].
      pose proof
        (jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs H codec τ k HT
           (Hrel k (or_introl eq_refl)))
        as [Htask [Hidx _]].
      pose proof
        (jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs H codec τ k' HT
           (Hrel k' (or_intror Hin')))
        as [Htask' [Hidx' _]].
      subst j'.
      simpl in Heq.
      injection Heq as Heq_task Heq_idx.
      rewrite Htask in Heq_task.
      rewrite Htask' in Heq_task.
      rewrite Hidx in Heq_idx.
      rewrite Hidx' in Heq_idx.
      subst.
      contradiction.
    + apply IH.
      intros k0 Hin0.
      exact (Hrel k0 (or_intror Hin0)).
Qed.

Lemma enum_jittered_periodic_jobs_upto_unfiltered_task_index_nodup :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup
      (map (fun j => (job_task (jobs j), job_index (jobs j)))
           (enum_jittered_periodic_jobs_upto_unfiltered
              T tasks offset jitter jobs H enumT codec)).
Proof.
  intros T tasks offset jitter jobs H enumT codec HnodupT HenumT.
  induction HnodupT as [|τ enumT Hnotin Hnodup IH]; simpl.
  - constructor.
  - rewrite map_app.
    assert (Hhead :
      NoDup
        (map (fun j => (job_task (jobs j), job_index (jobs j)))
             (map (jittered_periodic_job_id_of
                     T tasks offset jitter jobs H codec τ)
                  (enum_jittered_periodic_indices_upto tasks offset τ H)))).
    { apply enum_jittered_periodic_jobs_upto_task_index_nodup_for_task.
      - exact (HenumT τ (or_introl eq_refl)).
      - intros k Hk.
        apply in_enum_jittered_periodic_indices_upto_iff in Hk.
        exact (proj2 Hk).
      - apply NoDup_filter.
        apply seq_NoDup.
    }
    assert (Hdisjoint :
      forall p,
        In p
          (map (fun j => (job_task (jobs j), job_index (jobs j)))
               (map (jittered_periodic_job_id_of
                       T tasks offset jitter jobs H codec τ)
                    (enum_jittered_periodic_indices_upto tasks offset τ H))) ->
        ~ In p
            (map (fun j => (job_task (jobs j), job_index (jobs j)))
                 (enum_jittered_periodic_jobs_upto_unfiltered
                    T tasks offset jitter jobs H enumT codec))).
    { intros [τ' k'] HinHead HinTail.
      apply in_map_iff in HinHead.
      destruct HinHead as [j0 [HeqHead Hinj0]].
      apply in_map_iff in Hinj0.
      destruct Hinj0 as [k [Hj0_eq Hkin]].
      unfold enum_jittered_periodic_jobs_upto_unfiltered in HinTail.
      apply in_map_iff in HinTail.
      destruct HinTail as [j [Hpair Hj]].
      apply in_flat_map in Hj.
      destruct Hj as [τ'' [Hτ''in Hjmap]].
      apply in_map_iff in Hjmap.
      destruct Hjmap as [k'' [Hj_eq Hkin'']].
      assert (Hrel : expected_release tasks offset τ k < H).
      { exact
          (proj2
             (proj1
                (in_enum_jittered_periodic_indices_upto_iff
                   tasks offset τ H k) Hkin)). }
      assert (Hrel'' : expected_release tasks offset τ'' k'' < H).
      { exact
          (proj2
             (proj1
                (in_enum_jittered_periodic_indices_upto_iff
                   tasks offset τ'' H k'') Hkin'')). }
      pose proof
        (jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs H codec τ k
           (HenumT τ (or_introl eq_refl)) Hrel)
        as [Htask [Hidx _]].
      pose proof
        (jittered_periodic_job_id_of_sound
           T tasks offset jitter jobs H codec τ'' k''
           (HenumT τ'' (or_intror Hτ''in)) Hrel'')
        as [Htask'' [Hidx'' _]].
      subst j0.
      simpl in HeqHead.
      injection HeqHead as HeqTask HeqIdx.
      subst j.
      simpl in Hpair.
      injection Hpair as HeqTask' HeqIdx'.
      rewrite Htask in HeqTask.
      rewrite Hidx in HeqIdx.
      rewrite Htask'' in HeqTask'.
      rewrite Hidx'' in HeqIdx'.
      subst.
      contradiction.
    }
    assert (IH' :
      NoDup
        (map (fun j => (job_task (jobs j), job_index (jobs j)))
             (enum_jittered_periodic_jobs_upto_unfiltered
                T tasks offset jitter jobs H enumT codec))).
    { apply IH.
      intros τ' Hin.
      apply HenumT.
      now right.
    }
    clear IH.
    induction Hhead as [|p l HninHead HnodupHead IHhead].
    + exact IH'.
    + constructor.
      * intro Hin.
        apply in_app_or in Hin.
        destruct Hin as [Hin | Hin].
        -- apply HninHead. exact Hin.
        -- exact (Hdisjoint p (or_introl eq_refl) Hin).
      * apply IHhead.
        intros p0 Hin0.
        exact (Hdisjoint p0 (or_intror Hin0)).
Qed.

Lemma jittered_periodic_job_list_pair_nodup_implies_nodup :
  forall (jobs : JobId -> Job) (l : list JobId),
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    NoDup l.
Proof.
  intros jobs l Hpairs.
  induction l as [|j l IH]; simpl in *.
  - constructor.
  - inversion Hpairs as [|p ps HnotinPairs HpairsTail]; subst p ps.
    constructor.
    + intro Hin.
      apply HnotinPairs.
      exact (in_map (fun j0 => (job_task (jobs j0), job_index (jobs j0))) l j Hin).
    + apply IH.
      exact HpairsTail.
Qed.

Lemma enum_jittered_periodic_jobs_upto_nodup :
  forall T tasks offset jitter jobs H enumT
         (codec : JitteredPeriodicFiniteHorizonCodec
                    T tasks offset jitter jobs H),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup
      (enum_jittered_periodic_jobs_upto
         T tasks offset jitter jobs H enumT codec).
Proof.
  intros T tasks offset jitter jobs H enumT codec HnodupT HenumT.
  unfold enum_jittered_periodic_jobs_upto.
  eapply NoDup_filter.
  eapply jittered_periodic_job_list_pair_nodup_implies_nodup.
  eapply enum_jittered_periodic_jobs_upto_unfiltered_task_index_nodup; eauto.
Qed.

Definition enum_jittered_periodic_jobs_before
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jitter : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : JitteredPeriodicCodec T tasks offset jitter jobs)
    (t : Time)
    : list JobId :=
  enum_jittered_periodic_jobs_upto
    T tasks offset jitter jobs t enumT
    (jittered_periodic_finite_horizon_codec_of
       T tasks offset jitter jobs t codec).

Lemma enum_jittered_periodic_jobs_before_sound :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    (forall τ, In τ enumT -> T τ) ->
    forall t j,
      In j (enum_jittered_periodic_jobs_before
              T tasks offset jitter jobs enumT codec t) ->
      jittered_periodic_jobset T tasks offset jitter jobs j /\
      job_release (jobs j) < t.
Proof.
  intros T tasks offset jitter jobs enumT codec HenumT_sound t j Hj.
  unfold enum_jittered_periodic_jobs_before in Hj.
  pose proof
    (enum_jittered_periodic_jobs_upto_sound
       T tasks offset jitter jobs t enumT
       (jittered_periodic_finite_horizon_codec_of
          T tasks offset jitter jobs t codec)
       HenumT_sound j Hj) as Hjobset.
  split.
  - exact
      (jittered_periodic_jobset_upto_implies_jittered_periodic_jobset
         T tasks offset jitter jobs t j Hjobset).
  - exact
      (jittered_periodic_jobset_upto_implies_release_lt
         T tasks offset jitter jobs t j Hjobset).
Qed.

Lemma enum_jittered_periodic_jobs_before_complete :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    forall t j,
      jittered_periodic_jobset T tasks offset jitter jobs j ->
      job_release (jobs j) < t ->
      In j (enum_jittered_periodic_jobs_before
              T tasks offset jitter jobs enumT codec t).
Proof.
  intros T tasks offset jitter jobs enumT codec Hwf HenumT_complete t j Hjobset Hrel.
  unfold enum_jittered_periodic_jobs_before.
  eapply enum_jittered_periodic_jobs_upto_complete.
  - exact Hwf.
  - exact HenumT_complete.
  - exact
      (jittered_periodic_jobset_with_release_lt_implies_upto
         T tasks offset jitter jobs t j Hjobset Hrel).
Qed.

Lemma enum_jittered_periodic_jobs_before_nodup :
  forall T tasks offset jitter jobs enumT
         (codec : JitteredPeriodicCodec T tasks offset jitter jobs),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    forall t,
      NoDup
        (enum_jittered_periodic_jobs_before
           T tasks offset jitter jobs enumT codec t).
Proof.
  intros T tasks offset jitter jobs enumT codec HnodupT HenumT t.
  unfold enum_jittered_periodic_jobs_before.
  apply enum_jittered_periodic_jobs_upto_nodup; assumption.
Qed.
