From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
Import ListNotations.

(* ===== Boolean task-list membership ===== *)

(* Test whether τ appears in a list of TaskIds. *)
Definition task_in_list_b (enumT : list TaskId) (τ : TaskId) : bool :=
  existsb (Nat.eqb τ) enumT.

Lemma task_in_list_b_spec :
  forall enumT τ,
    task_in_list_b enumT τ = true <-> In τ enumT.
Proof.
  intros enumT τ.
  unfold task_in_list_b.
  rewrite existsb_exists.
  split.
  - intros [x [Hin Heqb]].
    apply Nat.eqb_eq in Heqb.
    subst x. exact Hin.
  - intros Hin.
    exists τ. split.
    + exact Hin.
    + apply Nat.eqb_refl.
Qed.

(* ===== Finite-horizon codec ===== *)

(* A PeriodicFiniteHorizonCodec provides a canonical mapping
   (task τ, index k) → JobId that is:
   - sound: if τ is in scope and expected_release < H,
     then the mapped job has the right task/index/generation;
   - complete: every job in the jobset equals the mapped job
     for its task and index. *)
Record PeriodicFiniteHorizonCodec
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time) : Type := mkPeriodicFiniteHorizonCodec {

  periodic_job_id_of : TaskId -> nat -> JobId;

  periodic_job_id_of_sound :
    forall τ k,
      T τ ->
      expected_release tasks offset τ k < H ->
      let j := periodic_job_id_of τ k in
      job_task (jobs j) = τ /\
      job_index (jobs j) = k /\
      generated_by_periodic_task tasks offset jobs j;

  periodic_job_id_of_complete :
    forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      j = periodic_job_id_of (job_task (jobs j)) (job_index (jobs j))
}.

Definition periodic_finite_horizon_codec_of
    T tasks offset jobs H
    (codec : PeriodicCodec T tasks offset jobs)
  : PeriodicFiniteHorizonCodec T tasks offset jobs H.
Proof.
  refine
    (mkPeriodicFiniteHorizonCodec
       T tasks offset jobs H
       (global_periodic_job_id_of T tasks offset jobs codec) _ _).
  - intros τ k HT _.
    exact (global_periodic_job_id_of_sound T tasks offset jobs codec τ k HT).
  - intros j Hjobset.
    apply global_periodic_job_id_of_complete.
    exact (periodic_jobset_upto_implies_periodic_jobset
             T tasks offset jobs H j Hjobset).
Defined.

(* ===== Index enumeration ===== *)

(* Enumerate all k in [0, H) whose expected release is also < H. *)
Definition enum_periodic_indices_upto
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (τ : TaskId)
    (H : Time) : list nat :=
  filter
    (fun k => Nat.ltb (expected_release tasks offset τ k) H)
    (seq 0 H).

Lemma in_enum_periodic_indices_upto_iff :
  forall tasks offset τ H k,
    In k (enum_periodic_indices_upto tasks offset τ H) <->
    k < H /\ expected_release tasks offset τ k < H.
Proof.
  intros tasks offset τ H k.
  unfold enum_periodic_indices_upto.
  rewrite filter_In.
  rewrite in_seq.
  rewrite Nat.ltb_lt.
  split.
  - intros [[_ Hk] Hrel]. split; [exact Hk | exact Hrel].
  - intros [Hk Hrel]. split; [split; [lia | exact Hk] | exact Hrel].
Qed.

(* ===== Job enumeration ===== *)

(* Build the full list of JobIds for the periodic jobset up to H,
   from a task enumeration list and a codec. *)
Definition enum_periodic_jobs_upto
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (H : Time)
    (enumT : list TaskId)
    (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
    : list JobId :=
  let id_of := periodic_job_id_of T tasks offset jobs H codec in
  flat_map
    (fun τ => map (id_of τ) (enum_periodic_indices_upto tasks offset τ H))
    enumT.

(* ===== Soundness ===== *)

Lemma enum_periodic_jobs_upto_sound :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    (forall τ, In τ enumT -> T τ) ->
    forall j,
      In j (enum_periodic_jobs_upto T tasks offset jobs H enumT codec) ->
      periodic_jobset_upto T tasks offset jobs H j.
Proof.
  intros T tasks offset jobs H enumT codec HenumT_sound j Hj.
  unfold enum_periodic_jobs_upto in Hj.
  apply in_flat_map in Hj.
  destruct Hj as [τ [HτinT Hjinmap]].
  apply in_map_iff in Hjinmap.
  destruct Hjinmap as [k [Hjk Hkin]].
  apply in_enum_periodic_indices_upto_iff in Hkin.
  destruct Hkin as [_ Hrel].
  subst j.
  pose proof (HenumT_sound τ HτinT) as HT.
  pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ k HT Hrel)
    as [Htask [Hidx Hgen]].
  unfold periodic_jobset_upto.
  split.
  - rewrite Htask. exact HT.
  - split.
    + exact Hgen.
    + rewrite (generated_job_release tasks offset jobs _ Hgen).
      rewrite Htask. rewrite Hidx. exact Hrel.
Qed.

(* ===== Completeness ===== *)

Lemma enum_periodic_jobs_upto_complete :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    forall j,
      periodic_jobset_upto T tasks offset jobs H j ->
      In j (enum_periodic_jobs_upto T tasks offset jobs H enumT codec).
Proof.
  intros T tasks offset jobs H enumT codec Hwf HenumT_complete j Hjobset.
  pose proof (periodic_jobset_upto_implies_task_in_scope T tasks offset jobs H j Hjobset) as HT.
  pose proof (HenumT_complete _ HT) as HτinT.
  pose proof (periodic_jobset_upto_implies_index_lt T tasks offset jobs H j Hwf Hjobset) as Hk_lt.
  pose proof (periodic_jobset_upto_expected_release_lt T tasks offset jobs H j Hjobset) as Hrelease_lt.
  pose proof (periodic_job_id_of_complete T tasks offset jobs H codec j Hjobset) as Hjcodec.
  unfold enum_periodic_jobs_upto.
  apply in_flat_map.
  exists (job_task (jobs j)).
  split.
  - exact HτinT.
  - apply in_map_iff.
    exists (job_index (jobs j)).
    split.
    + symmetry. exact Hjcodec.
    + apply in_enum_periodic_indices_upto_iff.
      split; [exact Hk_lt | exact Hrelease_lt].
Qed.

Lemma enum_periodic_jobs_upto_task_index_nodup_for_task :
  forall T tasks offset jobs H τ ks
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    T τ ->
    (forall k, In k ks -> expected_release tasks offset τ k < H) ->
    NoDup ks ->
    NoDup
      (map (fun j => (job_task (jobs j), job_index (jobs j)))
           (map (periodic_job_id_of T tasks offset jobs H codec τ) ks)).
Proof.
  intros T tasks offset jobs H τ ks codec HT Hrel.
  induction 1 as [|k ks Hnin Hnodup IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [j' [Heq Hinj']].
      apply in_map_iff in Hinj'.
      destruct Hinj' as [k' [Hj'_eq Hin']].
      pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ k HT
                    (Hrel k (or_introl eq_refl)))
        as [Htask [Hidx _]].
      pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ k' HT
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

Lemma enum_periodic_jobs_upto_task_index_nodup :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup
      (map (fun j => (job_task (jobs j), job_index (jobs j)))
           (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)).
Proof.
  intros T tasks offset jobs H enumT codec HnodupT HenumT.
  induction HnodupT as [|τ enumT Hnotin Hnodup IH]; simpl.
  - constructor.
  - rewrite map_app.
    assert (Hhead :
      NoDup
        (map (fun j => (job_task (jobs j), job_index (jobs j)))
             (map (periodic_job_id_of T tasks offset jobs H codec τ)
                  (enum_periodic_indices_upto tasks offset τ H)))).
    { apply enum_periodic_jobs_upto_task_index_nodup_for_task.
      - exact (HenumT τ (or_introl eq_refl)).
      - intros k Hk.
        apply in_enum_periodic_indices_upto_iff in Hk.
        exact (proj2 Hk).
      - apply NoDup_filter.
        apply seq_NoDup.
    }
    assert (Hdisjoint :
      forall p,
        In p
          (map (fun j => (job_task (jobs j), job_index (jobs j)))
               (map (periodic_job_id_of T tasks offset jobs H codec τ)
                    (enum_periodic_indices_upto tasks offset τ H))) ->
        ~ In p
            (map (fun j => (job_task (jobs j), job_index (jobs j)))
                 (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))).
    { intros [τ' k'] HinHead HinTail.
      apply in_map_iff in HinHead.
      destruct HinHead as [j0 [HeqHead Hinj0]].
      apply in_map_iff in Hinj0.
      destruct Hinj0 as [k [Hj0_eq Hkin]].
      unfold enum_periodic_jobs_upto in HinTail.
      apply in_map_iff in HinTail.
      destruct HinTail as [j [Hpair Hj]].
      apply in_flat_map in Hj.
      destruct Hj as [τ'' [Hτ''in Hjmap]].
      apply in_map_iff in Hjmap.
      destruct Hjmap as [k'' [Hj_eq Hkin'']].
      assert (Hrel : expected_release tasks offset τ k < H).
      { exact (proj2 (proj1 (in_enum_periodic_indices_upto_iff tasks offset τ H k) Hkin)). }
      assert (Hrel'' : expected_release tasks offset τ'' k'' < H).
      { exact (proj2 (proj1 (in_enum_periodic_indices_upto_iff tasks offset τ'' H k'') Hkin'')). }
      pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ k
                    (HenumT τ (or_introl eq_refl)) Hrel)
        as [Htask [Hidx _]].
      pose proof (periodic_job_id_of_sound T tasks offset jobs H codec τ'' k''
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
             (enum_periodic_jobs_upto T tasks offset jobs H enumT codec))).
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

Lemma codec_periodic_jobs_same_task_index_eq :
  forall T tasks offset jobs H
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         j1 j2,
    periodic_jobset_upto T tasks offset jobs H j1 ->
    periodic_jobset_upto T tasks offset jobs H j2 ->
    job_task (jobs j1) = job_task (jobs j2) ->
    job_index (jobs j1) = job_index (jobs j2) ->
    j1 = j2.
Proof.
  intros T tasks offset jobs H codec j1 j2 Hj1 Hj2 Htask Hidx.
  rewrite (periodic_job_id_of_complete T tasks offset jobs H codec j1 Hj1).
  rewrite (periodic_job_id_of_complete T tasks offset jobs H codec j2 Hj2).
  now rewrite Htask, Hidx.
Qed.

Lemma periodic_job_list_pair_nodup_implies_nodup :
  forall T tasks offset jobs H
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H)
         l,
    (forall j, In j l -> periodic_jobset_upto T tasks offset jobs H j) ->
    NoDup (map (fun j => (job_task (jobs j), job_index (jobs j))) l) ->
    NoDup l.
Proof.
  intros T tasks offset jobs H codec l Hjobset Hpairs.
  induction l as [|j l IH]; simpl in *.
  - constructor.
  - inversion Hpairs as [|p ps HnotinPairs HpairsTail]; subst p ps.
    constructor.
    + intro Hin.
      apply HnotinPairs.
      exact (in_map (fun j0 => (job_task (jobs j0), job_index (jobs j0))) l j Hin).
    + apply IH.
      * intros j' Hin'.
        apply Hjobset. now right.
      * exact HpairsTail.
Qed.

Lemma enum_periodic_jobs_upto_nodup :
  forall T tasks offset jobs H enumT
         (codec : PeriodicFiniteHorizonCodec T tasks offset jobs H),
    NoDup enumT ->
    (forall τ, In τ enumT -> T τ) ->
    NoDup (enum_periodic_jobs_upto T tasks offset jobs H enumT codec).
Proof.
  intros T tasks offset jobs H enumT codec HnodupT HenumT.
  eapply (periodic_job_list_pair_nodup_implies_nodup
            T tasks offset jobs H codec
            (enum_periodic_jobs_upto T tasks offset jobs H enumT codec)).
  - intros j Hj.
    eapply enum_periodic_jobs_upto_sound; eauto.
  - eapply enum_periodic_jobs_upto_task_index_nodup; eauto.
Qed.

(* ===== Released-prefix enumeration via the global codec ===== *)

Definition enum_periodic_jobs_before
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (t : Time)
    : list JobId :=
  enum_periodic_jobs_upto
    T tasks offset jobs t enumT
    (periodic_finite_horizon_codec_of T tasks offset jobs t codec).

Lemma enum_periodic_jobs_before_sound :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    (forall τ, In τ enumT -> T τ) ->
    forall t j,
      In j (enum_periodic_jobs_before T tasks offset jobs enumT codec t) ->
      periodic_jobset T tasks offset jobs j /\
      job_release (jobs j) < t.
Proof.
  intros T tasks offset jobs enumT codec HenumT_sound t j Hj.
  unfold enum_periodic_jobs_before in Hj.
  pose proof
    (enum_periodic_jobs_upto_sound
       T tasks offset jobs t enumT
       (periodic_finite_horizon_codec_of T tasks offset jobs t codec)
       HenumT_sound j Hj) as Hjobset.
  split.
  - exact (periodic_jobset_upto_implies_periodic_jobset
             T tasks offset jobs t j Hjobset).
  - exact (periodic_jobset_upto_implies_release_lt
             T tasks offset jobs t j Hjobset).
Qed.

Lemma enum_periodic_jobs_before_complete :
  forall T tasks offset jobs enumT
         (codec : PeriodicCodec T tasks offset jobs),
    well_formed_periodic_tasks_on T tasks ->
    (forall τ, T τ -> In τ enumT) ->
    forall t j,
      periodic_jobset T tasks offset jobs j ->
      job_release (jobs j) < t ->
      In j (enum_periodic_jobs_before T tasks offset jobs enumT codec t).
Proof.
  intros T tasks offset jobs enumT codec Hwf HenumT_complete t j Hjobset Hrel.
  unfold enum_periodic_jobs_before.
  eapply enum_periodic_jobs_upto_complete.
  - exact Hwf.
  - exact HenumT_complete.
  - split.
    + exact (periodic_jobset_implies_task_in_scope T tasks offset jobs j Hjobset).
    + split.
      * exact (periodic_jobset_implies_generated T tasks offset jobs j Hjobset).
      * exact Hrel.
Qed.
