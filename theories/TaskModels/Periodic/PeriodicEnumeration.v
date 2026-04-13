From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicTasks.
From SchedulingTheory Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
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
