From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.OSCandidateSourceContract.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSSchedulerViewContract.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadAcceptance.
From RocqSched Require Import Operational.Awkernel.Minimal.WorkloadCandidateTable.

Definition empty_sched_trace_entry : AwkernelSchedTraceEntry :=
  mkAwkernelSchedTraceEntry 0 EvStutter None [] false None.

Definition workload_execution_matches_sched_trace
    {P : OSLabeledProjection AwkernelState}
    (ex : labeled_concrete_execution P 2)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  forall t,
    os_to_op_state (osl_to_os_projection P) (lce_trace ex t) =
    awk_to_op_state
      (awk_sched_trace_entry_to_state (nth t sched_trace empty_sched_trace_entry)).

Definition accepted_workload_candidate_source_family
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry)
    (table : list (list JobId)) : Prop :=
  accepted_workload_sched_trace_family task_trace sched_trace /\
  workload_candidate_table_contract sched_trace table.

Lemma job_in_listb_sound :
  forall j xs,
    job_in_listb j xs = true ->
    In j xs.
Proof.
  intros j xs.
  induction xs as [|x xs IH]; intros Hin; simpl in Hin.
  - discriminate.
  - apply Bool.orb_true_iff in Hin.
    destruct Hin as [Heq | Hin].
    + apply Nat.eqb_eq in Heq. subst x. left. reflexivity.
    + right. apply IH. exact Hin.
Qed.

Lemma job_in_optionb_sound :
  forall oj j,
    job_in_optionb oj j = true ->
    oj = Some j.
Proof.
  intros [j'|] j H; simpl in H.
  - apply Nat.eqb_eq in H. subst j'. reflexivity.
  - discriminate.
Qed.

Lemma all_jobs_includedb_sound :
  forall jobs cand j,
    all_jobs_includedb jobs cand = true ->
    In j jobs ->
    In j cand.
Proof.
  intros jobs.
  induction jobs as [|j' jobs IH]; intros cand j Hin Hall; simpl in *.
  - contradiction.
  - apply Bool.andb_true_iff in Hin as [Hj' Hrest].
    destruct Hall as [Heq | Hinjobs].
    + subst j'. apply job_in_listb_sound. exact Hj'.
    + apply IH; assumption.
Qed.

Lemma all_candidates_visibleb_sound :
  forall row cand j,
    all_candidates_visibleb row cand = true ->
    In j cand ->
    row_candidate_visibleb row j = true.
Proof.
  intros row cand.
  induction cand as [|j' cand IH]; intros j Hvisible Hin; simpl in *.
  - contradiction.
  - apply Bool.andb_true_iff in Hvisible as [Hhead Htail].
    destruct Hin as [Heq | Hin].
    + subst j. exact Hhead.
    + apply IH; assumption.
Qed.

Lemma row_candidate_visibleb_sound :
  forall row j,
    aste_cpu row < 2 ->
    row_candidate_visibleb row j = true ->
    op_job_visible 2 (awk_to_op_state (awk_sched_trace_entry_to_state row)) j.
Proof.
  intros row j Hcpu Hvisible.
  unfold row_candidate_visibleb in Hvisible.
  apply Bool.orb_true_iff in Hvisible.
  destruct Hvisible as [Hvisible | Htarget].
  - apply Bool.orb_true_iff in Hvisible.
    destruct Hvisible as [Hcurrent | Hrunnable].
    + left.
      exists (aste_cpu row).
      split; [assumption|].
      unfold awk_sched_trace_entry_to_state, awk_to_op_state.
      simpl.
      destruct (aste_current row) as [j'|] eqn:Hcur; simpl in Hcurrent; try discriminate.
      apply Nat.eqb_eq in Hcurrent.
      subst j'.
      rewrite Nat.eqb_refl.
      reflexivity.
    + right. left.
      unfold awk_sched_trace_entry_to_state, awk_to_op_state.
      simpl.
      apply job_in_listb_sound.
      exact Hrunnable.
  - right. right.
    exists (aste_cpu row).
    split; [assumption|].
    unfold awk_sched_trace_entry_to_state, awk_to_op_state.
    simpl.
    destruct (aste_dispatch_target row) as [j'|] eqn:Hdispatch;
      simpl in Htarget; try discriminate.
    apply Nat.eqb_eq in Htarget.
    subst j'.
    rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Lemma awk_sched_trace_state_current_inv :
  forall row c j,
    op_current (awk_to_op_state (awk_sched_trace_entry_to_state row)) c = Some j ->
    aste_current row = Some j /\ c = aste_cpu row.
Proof.
  intros row c j Hcur.
  unfold awk_sched_trace_entry_to_state, awk_to_op_state in Hcur.
  simpl in Hcur.
  destruct (aste_current row) as [j'|] eqn:Hentry; simpl in Hcur; try discriminate.
  destruct (Nat.eqb c (aste_cpu row)) eqn:Hcpu; inversion Hcur; subst j.
  apply Nat.eqb_eq in Hcpu.
  split; assumption.
Qed.

Lemma awk_sched_trace_state_dispatch_target_inv :
  forall row c j,
    op_dispatch_target (awk_to_op_state (awk_sched_trace_entry_to_state row)) c = Some j ->
    aste_dispatch_target row = Some j /\ c = aste_cpu row.
Proof.
  intros row c j Htarget.
  unfold awk_sched_trace_entry_to_state, awk_to_op_state in Htarget.
  simpl in Htarget.
  destruct (aste_dispatch_target row) as [j'|] eqn:Hentry;
    simpl in Htarget; try discriminate.
  destruct (Nat.eqb c (aste_cpu row)) eqn:Hcpu; inversion Htarget; subst j.
  apply Nat.eqb_eq in Hcpu.
  split; assumption.
Qed.

Lemma Forall2_nth_error_some :
  forall A B (R : A -> B -> Prop) xs ys n x y,
    Forall2 R xs ys ->
    nth_error xs n = Some x ->
    nth_error ys n = Some y ->
    R x y.
Proof.
  intros A B R xs ys n.
  revert xs ys.
  induction n as [|n IH]; intros xs ys x y Hfor Hx Hy.
  - destruct Hfor; simpl in *; try discriminate.
    inversion Hx; inversion Hy; subst.
    assumption.
  - destruct Hfor; simpl in *; try discriminate.
    eapply IH; eauto.
Qed.

Lemma workload_candidate_table_contract_nth :
  forall sched_trace table t row cand,
    workload_candidate_table_contract sched_trace table ->
    nth_error sched_trace t = Some row ->
    nth_error table t = Some cand ->
    workload_candidate_row_contract row cand.
Proof.
  intros sched_trace table t row cand [_ Hrows] Hrow Hcand.
  eapply Forall2_nth_error_some; eauto.
Qed.

Lemma candidate_source_of_table_in_bounds :
  forall table t j,
    In j (candidate_source_of_table table (fun _ => mkJob 0 0 0 0 1) 2 (fun _ _ => None) t) ->
    t < length table.
Proof.
  intros table t j Hin.
  unfold candidate_source_of_table in Hin.
  destruct (lt_dec t (length table)) as [Hlt | Hnlt].
  - exact Hlt.
  - rewrite nth_overflow in Hin by lia.
    contradiction.
Qed.

Lemma accepted_workload_candidate_source_sound_from_contract :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm
         (C : awk_local_adapter_contract P jobs adm 2)
         sched_trace table,
    Forall (fun entry => aste_cpu entry < 2) sched_trace ->
    workload_candidate_table_contract sched_trace table ->
    workload_execution_matches_sched_trace (olac_execution C) sched_trace ->
    awk_labeled_concrete_candidate_source_contract
      P
      jobs
      2
      (candidate_source_of_table table)
      (olac_execution C).
Proof.
  intros P jobs adm C sched_trace table Hcpus Htable Hmatch.
  refine
    {| lccsc_candidates_visible := _;
       lccsc_current_in_candidates := _;
       lccsc_runnable_in_candidates := _;
       lccsc_dispatch_target_in_candidates := _;
       lccsc_prefix_extensional := _ |}.
  - intros t j Hin.
    pose proof (candidate_source_of_table_in_bounds table t j Hin) as Ht.
    assert (Ht_rows : t < length sched_trace).
    { rewrite (proj1 Htable). exact Ht. }
    assert (Hrow : nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
    { apply nth_error_nth'. exact Ht_rows. }
    assert (Hcand : nth_error table t = Some (nth t table [])).
    { apply nth_error_nth'. exact Ht. }
    pose proof (workload_candidate_table_contract_nth
                  sched_trace table t
                  (nth t sched_trace empty_sched_trace_entry)
                  (nth t table [])
                  Htable Hrow Hcand) as Hrow_contract.
    destruct Hrow_contract as [_ [Hvisible [_ [_ _]]]].
    rewrite (Hmatch t).
    eapply row_candidate_visibleb_sound.
    + eapply Forall_nth; eauto.
    + eapply all_candidates_visibleb_sound; eauto.
  - intros t c j Hlt Hcur.
    rewrite Hmatch in Hcur.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow : nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand : nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [Hcurrent [_ _]]]].
      destruct (awk_sched_trace_state_current_inv
                  (nth t sched_trace empty_sched_trace_entry) c j Hcur) as [Hentry _].
      unfold option_candidate_includedb in Hcurrent.
      rewrite Hentry in Hcurrent.
      simpl in Hcurrent.
      apply job_in_listb_sound.
      exact Hcurrent.
    + rewrite nth_overflow in Hcur by lia.
      discriminate.
  - intros t j Hin.
    rewrite Hmatch in Hin.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow : nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand : nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [_ [Hrunnable _]]]].
      unfold awk_sched_trace_entry_to_state, awk_to_op_state in Hin.
      simpl in Hin.
      eapply all_jobs_includedb_sound; eauto.
    + rewrite nth_overflow in Hin by lia.
      contradiction.
  - intros t c j Hlt Hdispatch.
    rewrite Hmatch in Hdispatch.
    destruct (lt_dec t (length sched_trace)) as [Ht | Ht].
    + assert (Hrow : nth_error sched_trace t = Some (nth t sched_trace empty_sched_trace_entry)).
      { apply nth_error_nth'. exact Ht. }
      assert (Ht_table : t < length table).
      { rewrite <- (proj1 Htable). exact Ht. }
      assert (Hcand : nth_error table t = Some (nth t table [])).
      { apply nth_error_nth'. exact Ht_table. }
      pose proof (workload_candidate_table_contract_nth
                    sched_trace table t
                    (nth t sched_trace empty_sched_trace_entry)
                    (nth t table [])
                    Htable Hrow Hcand) as Hrow_contract.
      destruct Hrow_contract as [_ [_ [_ [_ Htarget]]]].
      destruct (awk_sched_trace_state_dispatch_target_inv
                  (nth t sched_trace empty_sched_trace_entry) c j Hdispatch) as [Hentry _].
      unfold option_candidate_includedb in Htarget.
      rewrite Hentry in Htarget.
      simpl in Htarget.
      apply job_in_listb_sound.
      exact Htarget.
    + rewrite nth_overflow in Hdispatch by lia.
      discriminate.
  - intros s1 s2 t Hprefix.
    apply candidate_source_of_table_prefix_extensional.
    exact Hprefix.
Qed.

Lemma accepted_workload_candidate_source_sound :
  forall (P : OSLabeledProjection AwkernelState)
         jobs adm
         (C : awk_local_adapter_contract P jobs adm 2)
         task_trace sched_trace table,
    accepted_workload_candidate_source_family task_trace sched_trace table ->
    workload_execution_matches_sched_trace (olac_execution C) sched_trace ->
    awk_labeled_concrete_candidate_source_contract
      P
      jobs
      2
      (candidate_source_of_table table)
      (olac_execution C).
Proof.
  intros P jobs adm C task_trace sched_trace table
         [Haccepted Htable] Hmatch.
  eapply accepted_workload_candidate_source_sound_from_contract.
  - eapply accepted_workload_sched_trace_family_cpus_in_range.
    exact Haccepted.
  - exact Htable.
  - exact Hmatch.
Qed.

Definition accepted_workload_candidate_source_adapter_contract
    (P : OSLabeledProjection AwkernelState)
    jobs adm
    (C : awk_local_adapter_contract P jobs adm 2)
    task_trace sched_trace table
    (Hfamily : accepted_workload_candidate_source_family task_trace sched_trace table)
    (Hmatch : workload_execution_matches_sched_trace (olac_execution C) sched_trace)
    : awk_local_candidate_source_adapter_contract
        P
        (candidate_source_of_table table)
        jobs
        adm
        2 :=
  {|
    olcsac_base := C;
    olcsac_candidates :=
      accepted_workload_candidate_source_sound
        P jobs adm C task_trace sched_trace table Hfamily Hmatch;
  |}.
