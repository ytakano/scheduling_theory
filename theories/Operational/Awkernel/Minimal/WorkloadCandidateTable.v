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
    (row : AwkernelSchedTraceEntry) (j : JobId) : bool :=
  job_in_optionb (sched_trace_primary_current row) j ||
  job_in_listb j (aste_runnable row) ||
  job_in_optionb (sched_trace_primary_dispatch_target row) j.

Fixpoint all_candidates_visibleb
    (row : AwkernelSchedTraceEntry) (cand : list JobId) : bool :=
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
    (row : AwkernelSchedTraceEntry) (cand : list JobId) : bool :=
  sorted_nodup_job_listb cand &&
  all_candidates_visibleb row cand &&
  option_candidate_includedb (sched_trace_primary_current row) cand &&
  all_jobs_includedb (aste_runnable row) cand &&
  option_candidate_includedb (sched_trace_primary_dispatch_target row) cand.

Fixpoint candidate_table_contractb
    (rows : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : bool :=
  match rows, table with
  | [], [] => true
  | row :: rows', cand :: table' =>
      candidate_row_contractb row cand &&
      candidate_table_contractb rows' table'
  | _, _ => false
  end.

Definition candidate_table_matches_rows
    (rows : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : bool :=
  Nat.eqb (length rows) (length table) &&
  candidate_table_contractb rows table.

Definition workload_candidate_row_contract
    (row : AwkernelSchedTraceEntry) (cand : list JobId) : Prop :=
  sorted_nodup_job_listb cand = true /\
  all_candidates_visibleb row cand = true /\
  option_candidate_includedb (sched_trace_primary_current row) cand = true /\
  all_jobs_includedb (aste_runnable row) cand = true /\
  option_candidate_includedb (sched_trace_primary_dispatch_target row) cand = true.

Definition workload_candidate_table_contract
    (rows : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : Prop :=
  length rows = length table /\
  Forall2 workload_candidate_row_contract rows table.

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
  forall row cand,
    candidate_row_contractb row cand = true ->
    workload_candidate_row_contract row cand.
Proof.
  intros row cand H.
  unfold candidate_row_contractb in H.
  apply Bool.andb_true_iff in H as [Hrest Hdispatch].
  apply Bool.andb_true_iff in Hrest as [Hrest Hrunnable].
  apply Bool.andb_true_iff in Hrest as [Hrest Hcurrent].
  apply Bool.andb_true_iff in Hrest as [Hsorted Hvisible].
  repeat split; assumption.
Qed.

Lemma candidate_row_contractb_complete :
  forall row cand,
    workload_candidate_row_contract row cand ->
    candidate_row_contractb row cand = true.
Proof.
  intros row cand [Hsorted [Hvisible [Hcurrent [Hrunnable Hdispatch]]]].
  unfold candidate_row_contractb.
  rewrite Hsorted, Hvisible, Hcurrent, Hrunnable, Hdispatch.
  reflexivity.
Qed.

Lemma candidate_table_contractb_sound :
  forall rows table,
    candidate_table_contractb rows table = true ->
    Forall2 workload_candidate_row_contract rows table.
Proof.
  intros rows.
  induction rows as [|row rows IH]; intros table H;
    destruct table as [|cand table]; simpl in H; try discriminate.
  - constructor.
  - apply Bool.andb_true_iff in H as [Hrow Hrest].
    constructor.
    + apply candidate_row_contractb_sound. exact Hrow.
    + apply IH. exact Hrest.
Qed.

Lemma candidate_table_contractb_complete :
  forall rows table,
    Forall2 workload_candidate_row_contract rows table ->
    candidate_table_contractb rows table = true.
Proof.
  intros rows table Hcontract.
  induction Hcontract; simpl.
  - reflexivity.
  - rewrite candidate_row_contractb_complete by exact H.
    rewrite IHHcontract.
    reflexivity.
Qed.

Lemma candidate_table_matches_rows_sound :
  forall rows table,
    candidate_table_matches_rows rows table = true ->
    workload_candidate_table_contract rows table.
Proof.
  intros rows table Hmatch.
  unfold candidate_table_matches_rows, workload_candidate_table_contract in Hmatch |- *.
  apply Bool.andb_true_iff in Hmatch as [Hlen Htable].
  apply Nat.eqb_eq in Hlen.
  split; [exact Hlen|].
  apply candidate_table_contractb_sound.
  exact Htable.
Qed.

Lemma candidate_table_matches_rows_complete :
  forall rows table,
    workload_candidate_table_contract rows table ->
    candidate_table_matches_rows rows table = true.
Proof.
  intros rows table [Hlen Hcontract].
  unfold candidate_table_matches_rows.
  assert (Nat.eqb (length rows) (length table) = true) as Hlenb.
  { apply Nat.eqb_eq. exact Hlen. }
  rewrite Hlenb.
  rewrite candidate_table_contractb_complete by exact Hcontract.
  reflexivity.
Qed.
