From Stdlib Require Import Arith Arith.PeanoNat Lia Bool List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
Import ListNotations.

Record PeriodicCodec
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job) : Type := mkPeriodicCodec {
  global_periodic_job_id_of : TaskId -> nat -> JobId;

  global_periodic_job_id_of_sound :
    forall τ k,
      T τ ->
      let j := global_periodic_job_id_of τ k in
      job_task (jobs j) = τ /\
      job_index (jobs j) = k /\
      generated_by_periodic_task tasks offset jobs j;

  global_periodic_job_id_of_complete :
    forall j,
      periodic_jobset T tasks offset jobs j ->
      j = global_periodic_job_id_of (job_task (jobs j)) (job_index (jobs j))
}.

Fixpoint task_position_in_enumT (enumT : list TaskId) (τ : TaskId) : nat :=
  match enumT with
  | [] => 0
  | x :: xs => if Nat.eqb x τ then 0 else S (task_position_in_enumT xs τ)
  end.

Definition encode_job_id_from_enumT
    (enumT : list TaskId) (τ : TaskId) (k : nat) : JobId :=
  task_position_in_enumT enumT τ + length enumT * k.

Definition decode_job_id_from_enumT
    (enumT : list TaskId) (j : JobId) : nat * nat :=
  match length enumT with
  | 0 => (0, j)
  | n => (j mod n, j / n)
  end.

Definition canonical_periodic_jobs_from_enumT
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (j : JobId) : Job :=
  let '(pos, k) := decode_job_id_from_enumT enumT j in
  match nth_error enumT pos with
  | Some τ => generated_periodic_job tasks offset τ k
  | None => mkJob 0 j 0 (S (task_cost (tasks 0))) 0
  end.

Lemma task_position_in_enumT_lt_length :
  forall enumT τ,
    In τ enumT ->
    task_position_in_enumT enumT τ < length enumT.
Proof.
  induction enumT as [|x xs IH]; intros τ Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + rewrite Nat.eqb_refl. simpl. lia.
    + destruct (Nat.eqb x τ) eqn:Heq.
      * simpl. lia.
      * simpl. specialize (IH _ Hin). lia.
Qed.

Lemma nth_error_task_position_in_enumT :
  forall enumT τ,
    NoDup enumT ->
    In τ enumT ->
    nth_error enumT (task_position_in_enumT enumT τ) = Some τ.
Proof.
  induction enumT as [|x xs IH]; intros τ Hnodup Hin; simpl in *.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct Hin as [-> | Hin].
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb x τ) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. contradiction.
      * apply IH; assumption.
Qed.

Lemma task_position_in_enumT_complete :
  forall enumT i τ,
    NoDup enumT ->
    nth_error enumT i = Some τ ->
    task_position_in_enumT enumT τ = i.
Proof.
  induction enumT as [|x xs IH]; intros i τ Hnodup Hnth; simpl in *.
  - destruct i; inversion Hnth.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    destruct i as [|i].
    + inversion Hnth; subst.
      rewrite Nat.eqb_refl. reflexivity.
    + simpl in Hnth.
      destruct (Nat.eqb x τ) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst.
        exfalso.
        apply nth_error_In in Hnth.
        pose proof Hnth as Hinxs.
        exact (Hnotin Hinxs).
      * f_equal. apply IH; assumption.
Qed.

Lemma decode_encode_job_id_from_enumT :
  forall enumT τ k,
    In τ enumT ->
    NoDup enumT ->
    let n := length enumT in
    n > 0 ->
    decode_job_id_from_enumT enumT (encode_job_id_from_enumT enumT τ k) =
      (task_position_in_enumT enumT τ, k).
Proof.
  intros enumT τ k Hin Hnodup n Hnpos.
  unfold decode_job_id_from_enumT, encode_job_id_from_enumT.
  destruct (length enumT) as [|n'] eqn:Hlen; [lia|].
  change
    ((((task_position_in_enumT enumT τ + S n' * k) mod S n'),
      ((task_position_in_enumT enumT τ + S n' * k) / S n')) =
     (task_position_in_enumT enumT τ, k)).
  assert (Hlt : task_position_in_enumT enumT τ < S n').
  { rewrite <- Hlen. apply task_position_in_enumT_lt_length. exact Hin. }
  f_equal.
  - symmetry.
    apply Nat.mod_unique with k.
    + exact Hlt.
    + lia.
  - symmetry.
    apply Nat.div_unique with (task_position_in_enumT enumT τ).
    + exact Hlt.
    + lia.
Qed.

Lemma decode_job_id_from_enumT_inj :
  forall enumT j1 j2,
    length enumT > 0 ->
    decode_job_id_from_enumT enumT j1 = decode_job_id_from_enumT enumT j2 ->
    j1 = j2.
Proof.
  intros enumT j1 j2 Hnonempty Hdecode.
  unfold decode_job_id_from_enumT in Hdecode.
  destruct (length enumT) as [|n] eqn:Hlen; [lia|].
  change (((j1 mod S n), (j1 / S n)) = ((j2 mod S n), (j2 / S n))) in Hdecode.
  pose proof (f_equal fst Hdecode) as Hmod.
  pose proof (f_equal snd Hdecode) as Hdiveq.
  change (j1 mod S n = j2 mod S n) in Hmod.
  change (j1 / S n = j2 / S n) in Hdiveq.
  pose proof (Nat.div_mod j1 (S n) ltac:(lia)) as Hj1.
  pose proof (Nat.div_mod j2 (S n) ltac:(lia)) as Hj2.
  rewrite Hj1, Hj2.
  rewrite Hmod, Hdiveq.
  reflexivity.
Qed.

Definition periodic_codec_of_enumT
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (enumT : list TaskId)
    (Hnodup : NoDup enumT)
    (Hcomplete : forall τ, T τ -> In τ enumT)
    (Hsound : forall τ, In τ enumT -> T τ)
    (Hnonempty : length enumT > 0)
  : PeriodicCodec T tasks offset (canonical_periodic_jobs_from_enumT tasks offset enumT).
Proof.
  refine
    (mkPeriodicCodec
       T tasks offset (canonical_periodic_jobs_from_enumT tasks offset enumT)
       (encode_job_id_from_enumT enumT) _ _).
  - intros τ k HT.
    pose proof (Hcomplete _ HT) as Hin.
    unfold canonical_periodic_jobs_from_enumT.
    rewrite (decode_encode_job_id_from_enumT enumT τ k Hin Hnodup Hnonempty).
    rewrite (nth_error_task_position_in_enumT enumT τ Hnodup Hin).
    split; [reflexivity | split; [reflexivity |]].
    unfold generated_by_periodic_task.
    rewrite (decode_encode_job_id_from_enumT enumT τ k Hin Hnodup Hnonempty).
    rewrite (nth_error_task_position_in_enumT enumT τ Hnodup Hin).
    unfold generated_periodic_job.
    cbn [job_task job_index job_release job_abs_deadline job_cost
         expected_release expected_abs_deadline].
    split; [reflexivity | split; [reflexivity | lia]].
  - intros j Hjobset.
    unfold canonical_periodic_jobs_from_enumT in Hjobset |- *.
    destruct (decode_job_id_from_enumT enumT j) as [pos k] eqn:Hdecode.
    destruct (nth_error enumT pos) as [τ|] eqn:Hnth.
    + assert (Hτ : T τ).
      { apply Hsound. eapply nth_error_In. exact Hnth. }
      assert (Hpos : task_position_in_enumT enumT τ = pos).
      { apply task_position_in_enumT_complete with (enumT := enumT); assumption. }
      eapply eq_sym.
      eapply decode_job_id_from_enumT_inj.
      * exact Hnonempty.
      * pose proof Hnth as Hinth.
        apply nth_error_In in Hinth.
        pose proof
          (decode_encode_job_id_from_enumT
             enumT τ k Hinth Hnodup Hnonempty) as Hencdec.
        rewrite Hpos in Hencdec.
        transitivity (pos, k).
        -- cbn [generated_periodic_job job_task job_index].
           exact Hencdec.
        -- exact (eq_sym Hdecode).
    + exfalso.
      unfold periodic_jobset in Hjobset.
      destruct Hjobset as [_ Hgen].
      unfold generated_by_periodic_task in Hgen.
      unfold canonical_periodic_jobs_from_enumT in Hgen.
      cbn [job_task job_index job_release job_cost job_abs_deadline] in Hgen.
      destruct Hgen as [_ [_ Hcost]].
      rewrite Hdecode in Hcost.
      rewrite Hnth in Hcost.
      cbn in Hcost.
      lia.
  Defined.

Definition zero_offset_periodic_codec_of_tasks
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (Hnodup : NoDup enumT)
    (Hcomplete : forall τ, T τ -> In τ enumT)
    (Hsound : forall τ, In τ enumT -> T τ)
    (Hnonempty : length enumT > 0)
  : PeriodicCodec T tasks (fun _ => 0) (canonical_periodic_jobs_from_enumT tasks (fun _ => 0) enumT) :=
  periodic_codec_of_enumT T tasks (fun _ => 0) enumT Hnodup Hcomplete Hsound Hnonempty.
