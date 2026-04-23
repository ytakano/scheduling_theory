From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
Import ListNotations.

Fixpoint job_in_listb (j : JobId) (xs : list JobId) : bool :=
  match xs with
  | [] => false
  | x :: xs' => Nat.eqb j x || job_in_listb j xs'
  end.

Definition job_in_optionb (oj : option JobId) (j : JobId) : bool :=
  match oj with
  | Some j' => Nat.eqb j j'
  | None => false
  end.

Fixpoint sorted_nodup_fromb (prev : JobId) (xs : list JobId) : bool :=
  match xs with
  | [] => true
  | x :: xs' => Nat.ltb prev x && sorted_nodup_fromb x xs'
  end.

Definition sorted_nodup_job_listb (xs : list JobId) : bool :=
  match xs with
  | [] => true
  | x :: xs' => sorted_nodup_fromb x xs'
  end.

Definition row_candidate_visibleb
    (row : AwkernelCapturedRow) (j : JobId) : bool :=
  job_in_optionb (acr_current row) j ||
  job_in_listb j (acr_runnable row) ||
  job_in_optionb (acr_dispatch_target row) j.

Fixpoint all_candidates_visibleb
    (row : AwkernelCapturedRow) (cand : list JobId) : bool :=
  match cand with
  | [] => true
  | j :: cand' =>
      row_candidate_visibleb row j && all_candidates_visibleb row cand'
  end.

Definition option_candidate_includedb
    (oj : option JobId) (cand : list JobId) : bool :=
  match oj with
  | Some j => job_in_listb j cand
  | None => true
  end.

Fixpoint all_jobs_includedb
    (jobs cand : list JobId) : bool :=
  match jobs with
  | [] => true
  | j :: jobs' => job_in_listb j cand && all_jobs_includedb jobs' cand
  end.

Definition candidate_row_contractb
    (known_tasks : list JobId)
    (row : AwkernelCapturedRow) (cand : list JobId) : bool :=
  sorted_nodup_job_listb cand &&
  all_candidates_visibleb row cand &&
  option_candidate_includedb (acr_current row) cand &&
  all_jobs_includedb (acr_runnable row) cand &&
  option_candidate_includedb (acr_dispatch_target row) cand &&
  all_jobs_includedb cand known_tasks.

Fixpoint candidate_table_contractb
    (known_tasks : list JobId)
    (rows : list AwkernelCapturedRow)
    (table : list (list JobId)) : bool :=
  match rows, table with
  | [], [] => true
  | row :: rows', cand :: table' =>
      candidate_row_contractb known_tasks row cand &&
      candidate_table_contractb known_tasks rows' table'
  | _, _ => false
  end.

Definition candidate_table_matches_rows
    (known_tasks : list JobId)
    (rows : list AwkernelCapturedRow)
    (table : list (list JobId)) : bool :=
  Nat.eqb (length rows) (length table) &&
  candidate_table_contractb known_tasks rows table.

Definition workload_candidate_row_contract
    (known_tasks : list JobId)
    (row : AwkernelCapturedRow) (cand : list JobId) : Prop :=
  sorted_nodup_job_listb cand = true /\
  all_candidates_visibleb row cand = true /\
  option_candidate_includedb (acr_current row) cand = true /\
  all_jobs_includedb (acr_runnable row) cand = true /\
  option_candidate_includedb (acr_dispatch_target row) cand = true /\
  all_jobs_includedb cand known_tasks = true.

Definition workload_candidate_table_contract
    (known_tasks : list JobId)
    (rows : list AwkernelCapturedRow)
    (table : list (list JobId)) : Prop :=
  length rows = length table /\
  Forall2 (workload_candidate_row_contract known_tasks) rows table.

Definition candidate_source_of_table
    (table : list (list JobId)) : CandidateSource :=
  fun _jobs _m _sched t => nth t table [].

Lemma candidate_source_of_table_prefix_extensional :
  forall table jobs m s1 s2 t,
    (forall t' c, t' < t -> s1 t' c = s2 t' c) ->
    candidate_source_of_table table jobs m s1 t =
    candidate_source_of_table table jobs m s2 t.
Proof.
  intros. reflexivity.
Qed.

Lemma candidate_row_contractb_sound :
  forall known_tasks row cand,
    candidate_row_contractb known_tasks row cand = true ->
    workload_candidate_row_contract known_tasks row cand.
Proof.
  intros known_tasks row cand H.
  unfold candidate_row_contractb in H.
  apply Bool.andb_true_iff in H as [Hrest Hknown].
  apply Bool.andb_true_iff in Hrest as [Hrest Hdispatch].
  apply Bool.andb_true_iff in Hrest as [Hrest Hrunnable].
  apply Bool.andb_true_iff in Hrest as [Hrest Hcurrent].
  apply Bool.andb_true_iff in Hrest as [Hsorted Hvisible].
  repeat split; assumption.
Qed.

Lemma candidate_table_contractb_sound :
  forall known_tasks rows table,
    candidate_table_contractb known_tasks rows table = true ->
    Forall2 (workload_candidate_row_contract known_tasks) rows table.
Proof.
  intros known_tasks rows.
  induction rows as [|row rows IH]; intros table H;
    destruct table as [|cand table]; simpl in H; try discriminate.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hrow Hrest].
    constructor.
    + apply candidate_row_contractb_sound. exact Hrow.
    + apply IH. exact Hrest.
Qed.

Lemma candidate_table_matches_rows_sound :
  forall known_tasks rows table,
    candidate_table_matches_rows known_tasks rows table = true ->
    workload_candidate_table_contract known_tasks rows table.
Proof.
  intros known_tasks rows table Hmatch.
  unfold candidate_table_matches_rows, workload_candidate_table_contract in Hmatch |- *.
  apply Bool.andb_true_iff in Hmatch as [Hlen Htable].
  apply Nat.eqb_eq in Hlen.
  split; [exact Hlen|].
  apply candidate_table_contractb_sound with (known_tasks := known_tasks).
  exact Htable.
Qed.
