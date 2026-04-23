From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
Import ListNotations.

Inductive AwkernelTaskTraceKind : Type :=
| LkSpawn
| LkRunnable
| LkChoose
| LkDispatch
| LkSleep
| LkJoinWait
| LkComplete.

Record AwkernelTaskTraceEntry : Type := mkAwkernelTaskTraceEntry {
  atte_kind : AwkernelTaskTraceKind;
  atte_subject : JobId;
  atte_related : option JobId;
}.

Definition option_job_eqb (x y : option JobId) : bool :=
  match x, y with
  | Some j1, Some j2 => Nat.eqb j1 j2
  | None, None => true
  | _, _ => false
  end.

Fixpoint job_list_contains (j : JobId) (xs : list JobId) : bool :=
  match xs with
  | [] => false
  | x :: xs' => Nat.eqb x j || job_list_contains j xs'
  end.

Fixpoint insert_job_sorted (j : JobId) (xs : list JobId) : list JobId :=
  match xs with
  | [] => [j]
  | x :: xs' =>
      if Nat.eqb j x then x :: xs'
      else if Nat.leb j x then j :: x :: xs'
      else x :: insert_job_sorted j xs'
  end.

Definition add_job_once (j : JobId) (xs : list JobId) : list JobId :=
  insert_job_sorted j xs.

Ltac peel_andb_left :=
  repeat match goal with
         | H : _ && _ = true |- _ =>
             apply Bool.andb_true_iff in H as [H _]
         end.

Fixpoint first_some {A B : Type}
    (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: xs' =>
      match f x with
      | Some y => Some y
      | None => first_some f xs'
      end
  end.

Fixpoint pair_list_contains (x : JobId * JobId) (xs : list (JobId * JobId)) : bool :=
  match xs with
  | [] => false
  | (a, b) :: xs' =>
      let '(x1, x2) := x in
      (Nat.eqb a x1 && Nat.eqb b x2) || pair_list_contains x xs'
  end.

Definition add_pair_once (x : JobId * JobId) (xs : list (JobId * JobId))
    : list (JobId * JobId) :=
  if pair_list_contains x xs then xs else x :: xs.

Fixpoint all_dependencies_completed
    (task_id : JobId)
    (deps : list (JobId * JobId))
    (completed : list JobId) : bool :=
  match deps with
  | [] => true
  | (waiter, child) :: deps' =>
      if Nat.eqb waiter task_id
      then job_list_contains child completed &&
           all_dependencies_completed task_id deps' completed
      else all_dependencies_completed task_id deps' completed
  end.

Definition bool_of_option_none (oj : option JobId) : bool :=
  match oj with
  | Some _ => false
  | None => true
  end.

Definition sched_trace_event_is_wakeup
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvWakeup j' => Nat.eqb j' j
  | _ => false
  end.

Definition sched_trace_event_is_choose
    (cpu j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvChoose c' j' => Nat.eqb c' cpu && Nat.eqb j' j
  | _ => false
  end.

Definition sched_trace_event_is_dispatch
    (cpu j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvDispatch c' j' => Nat.eqb c' cpu && Nat.eqb j' j
  | _ => false
  end.

Definition sched_trace_event_is_complete
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvComplete j' => Nat.eqb j' j
  | _ => false
  end.

Definition sched_trace_event_is_stutter
    (entry : AwkernelSchedTraceEntry) : bool :=
  match aste_event entry with
  | EvStutter => true
  | _ => false
  end.

Definition sched_trace_is_wakeup
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  Nat.eqb (aste_cpu entry) 0 &&
  sched_trace_event_is_wakeup j entry &&
  bool_of_option_none (aste_current entry) &&
  job_list_contains j (aste_runnable entry) &&
  Bool.eqb (aste_need_resched entry) false &&
  bool_of_option_none (aste_dispatch_target entry).

Definition sched_trace_is_choose
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  Nat.eqb (aste_cpu entry) 1 &&
  sched_trace_event_is_choose 1 j entry &&
  bool_of_option_none (aste_current entry) &&
  job_list_contains j (aste_runnable entry) &&
  Bool.eqb (aste_need_resched entry) false &&
  option_job_eqb (aste_dispatch_target entry) (Some j).

Definition sched_trace_is_dispatch
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  Nat.eqb (aste_cpu entry) 1 &&
  sched_trace_event_is_dispatch 1 j entry &&
  option_job_eqb (aste_current entry) (Some j) &&
  Bool.eqb (aste_need_resched entry) false &&
  bool_of_option_none (aste_dispatch_target entry).

Definition sched_trace_is_complete
    (j : JobId) (entry : AwkernelSchedTraceEntry) : bool :=
  Nat.eqb (aste_cpu entry) 1 &&
  sched_trace_event_is_complete j entry &&
  bool_of_option_none (aste_current entry) &&
  Bool.eqb (aste_need_resched entry) true &&
  bool_of_option_none (aste_dispatch_target entry).

Definition sched_trace_is_stutter
    (entry : AwkernelSchedTraceEntry) : bool :=
  Nat.eqb (aste_cpu entry) 1 &&
  sched_trace_event_is_stutter entry &&
  bool_of_option_none (aste_current entry) &&
  Bool.eqb (aste_need_resched entry) false &&
  bool_of_option_none (aste_dispatch_target entry).

Record AwkernelTaskTraceSummary : Type := mkAwkernelTaskTraceSummary {
  atts_root_task : option JobId;
  atts_known_tasks : list JobId;
  atts_completion_deps : list (JobId * JobId);
}.

Definition initial_task_trace_summary : AwkernelTaskTraceSummary :=
  mkAwkernelTaskTraceSummary None [] [].

Definition task_trace_entry_valid
    (summary : AwkernelTaskTraceSummary)
    (entry : AwkernelTaskTraceEntry) : bool :=
  match atte_kind entry with
  | LkSpawn =>
      negb (job_list_contains (atte_subject entry) (atts_known_tasks summary)) &&
      match atte_related entry with
      | None => option_job_eqb (atts_root_task summary) None
      | Some parent => job_list_contains parent (atts_known_tasks summary)
      end
  | LkJoinWait =>
      match atte_related entry with
      | Some child =>
          job_list_contains (atte_subject entry) (atts_known_tasks summary) &&
          job_list_contains child (atts_known_tasks summary)
      | None => false
      end
  | _ => job_list_contains (atte_subject entry) (atts_known_tasks summary)
  end.

Definition task_trace_entry_step
    (summary : AwkernelTaskTraceSummary)
    (entry : AwkernelTaskTraceEntry) : AwkernelTaskTraceSummary :=
  match atte_kind entry with
  | LkSpawn =>
      mkAwkernelTaskTraceSummary
        (match atte_related entry with
         | None => Some (atte_subject entry)
         | Some _ => atts_root_task summary
         end)
        (add_job_once (atte_subject entry) (atts_known_tasks summary))
        (atts_completion_deps summary)
  | LkJoinWait =>
      match atte_related entry with
      | Some child =>
          mkAwkernelTaskTraceSummary
            (atts_root_task summary)
            (atts_known_tasks summary)
            (add_pair_once (atte_subject entry, child) (atts_completion_deps summary))
      | None => summary
      end
  | _ => summary
  end.

Fixpoint summarize_task_trace
    (summary : AwkernelTaskTraceSummary)
    (task_trace : list AwkernelTaskTraceEntry)
    : option AwkernelTaskTraceSummary :=
  match task_trace with
  | [] => Some summary
  | entry :: task_trace' =>
      if task_trace_entry_valid summary entry
      then summarize_task_trace (task_trace_entry_step summary entry) task_trace'
      else None
  end.

Definition task_trace_well_formed
    (task_trace : list AwkernelTaskTraceEntry) : bool :=
  match summarize_task_trace initial_task_trace_summary task_trace with
  | Some _ => true
  | None => false
  end.

Record AwkernelSchedTraceAcceptanceState : Type := mkAwkernelSchedTraceAcceptanceState {
  astas_started : bool;
  astas_selected : option JobId;
  astas_dispatched : list JobId;
  astas_completed : list JobId;
}.

Definition initial_sched_trace_acceptance_state : AwkernelSchedTraceAcceptanceState :=
  mkAwkernelSchedTraceAcceptanceState false None [] [].

Definition sched_trace_step_start
    (summary : AwkernelTaskTraceSummary)
    (entry : AwkernelSchedTraceEntry) : option AwkernelSchedTraceAcceptanceState :=
  match atts_root_task summary with
  | Some root =>
      if sched_trace_is_wakeup root entry
      then Some (mkAwkernelSchedTraceAcceptanceState true None [] [])
      else None
  | None => None
  end.

Definition sched_trace_step_after_start
    (summary : AwkernelTaskTraceSummary)
    (st : AwkernelSchedTraceAcceptanceState)
    (entry : AwkernelSchedTraceEntry) : option AwkernelSchedTraceAcceptanceState :=
  let known := atts_known_tasks summary in
  let deps := atts_completion_deps summary in
  let try_wakeup_job (j : JobId) :=
      if sched_trace_is_wakeup j entry &&
         job_list_contains j known &&
         negb (job_list_contains j (astas_completed st))
      then Some st
      else None in
  let try_choose_job (j : JobId) :=
      if sched_trace_is_choose j entry &&
         job_list_contains j known &&
         negb (job_list_contains j (astas_completed st)) &&
         option_job_eqb (astas_selected st) None
      then Some (mkAwkernelSchedTraceAcceptanceState true (Some j) (astas_dispatched st) (astas_completed st))
      else None in
  let try_dispatch_job (j : JobId) :=
      if sched_trace_is_dispatch j entry &&
         option_job_eqb (astas_selected st) (Some j)
      then Some (mkAwkernelSchedTraceAcceptanceState true None (add_job_once j (astas_dispatched st)) (astas_completed st))
      else None in
  let try_complete_job (j : JobId) :=
      if sched_trace_is_complete j entry &&
         job_list_contains j (astas_dispatched st) &&
         negb (job_list_contains j (astas_completed st)) &&
         all_dependencies_completed j deps (astas_completed st)
      then Some (mkAwkernelSchedTraceAcceptanceState true None (astas_dispatched st) (add_job_once j (astas_completed st)))
      else None in
  if sched_trace_is_stutter entry
  then Some st
  else match first_some try_wakeup_job known with
       | Some st' => Some st'
       | None =>
           match first_some try_choose_job known with
           | Some st' => Some st'
           | None =>
               match first_some try_dispatch_job known with
               | Some st' => Some st'
               | None => first_some try_complete_job known
               end
           end
       end.

Definition sched_trace_step
    (summary : AwkernelTaskTraceSummary)
    (st : AwkernelSchedTraceAcceptanceState)
    (entry : AwkernelSchedTraceEntry) : option AwkernelSchedTraceAcceptanceState :=
  if astas_started st
  then sched_trace_step_after_start summary st entry
  else sched_trace_step_start summary entry.

Fixpoint accept_sched_trace_from
    (summary : AwkernelTaskTraceSummary)
    (st : AwkernelSchedTraceAcceptanceState)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  match sched_trace with
  | [] =>
      match atts_root_task summary with
      | Some root => job_list_contains root (astas_completed st)
      | None => false
      end
  | entry :: sched_trace' =>
      match sched_trace_step summary st entry with
      | Some st' => accept_sched_trace_from summary st' sched_trace'
      | None => false
      end
  end.

Definition sched_trace_family_member
    (summary : AwkernelTaskTraceSummary)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  accept_sched_trace_from summary initial_sched_trace_acceptance_state sched_trace.

Definition awk_workload_accepts_sched_trace
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : bool :=
  match summarize_task_trace initial_task_trace_summary task_trace with
  | Some summary => sched_trace_family_member summary sched_trace
  | None => false
  end.

Definition accepted_workload_sched_trace_family
    (task_trace : list AwkernelTaskTraceEntry)
    (sched_trace : list AwkernelSchedTraceEntry) : Prop :=
  exists summary,
    summarize_task_trace initial_task_trace_summary task_trace = Some summary /\
    sched_trace_family_member summary sched_trace = true.

Lemma awk_workload_accepts_sched_trace_sound :
  forall task_trace sched_trace,
    awk_workload_accepts_sched_trace task_trace sched_trace = true ->
    accepted_workload_sched_trace_family task_trace sched_trace.
Proof.
  intros task_trace sched_trace Haccept.
  unfold awk_workload_accepts_sched_trace in Haccept.
  destruct (summarize_task_trace initial_task_trace_summary task_trace) as [summary|] eqn:Hsummary;
    simpl in Haccept; try discriminate.
  exists summary.
  split; assumption.
Qed.

Lemma awk_workload_accepts_sched_trace_complete :
  forall task_trace sched_trace,
    accepted_workload_sched_trace_family task_trace sched_trace ->
    awk_workload_accepts_sched_trace task_trace sched_trace = true.
Proof.
  intros task_trace sched_trace [summary [Hsummary Hsched]].
  unfold awk_workload_accepts_sched_trace.
  rewrite Hsummary.
  exact Hsched.
Qed.

Lemma first_some_some :
  forall A B (f : A -> option B) xs y,
    first_some f xs = Some y ->
    exists x, In x xs /\ f x = Some y.
Proof.
  intros A B f xs.
  induction xs as [|x xs IH]; intros y Hsome; simpl in Hsome.
  - discriminate.
  - destruct (f x) as [y'|] eqn:Hfx.
    + inversion Hsome; subst y'.
      exists x. split; [left; reflexivity|assumption].
    + apply IH in Hsome.
      destruct Hsome as [x' [Hin Hfx']].
      exists x'. split; [right; assumption|assumption].
Qed.

Lemma sched_trace_is_wakeup_cpu_in_range :
  forall j entry,
    sched_trace_is_wakeup j entry = true ->
    aste_cpu entry < 2.
Proof.
  intros j entry H.
  unfold sched_trace_is_wakeup in H.
  peel_andb_left.
  apply Nat.eqb_eq in H.
  lia.
Qed.

Lemma sched_trace_is_choose_cpu_in_range :
  forall j entry,
    sched_trace_is_choose j entry = true ->
    aste_cpu entry < 2.
Proof.
  intros j entry H.
  unfold sched_trace_is_choose in H.
  peel_andb_left.
  apply Nat.eqb_eq in H.
  lia.
Qed.

Lemma sched_trace_is_dispatch_cpu_in_range :
  forall j entry,
    sched_trace_is_dispatch j entry = true ->
    aste_cpu entry < 2.
Proof.
  intros j entry H.
  unfold sched_trace_is_dispatch in H.
  peel_andb_left.
  apply Nat.eqb_eq in H.
  lia.
Qed.

Lemma sched_trace_is_complete_cpu_in_range :
  forall j entry,
    sched_trace_is_complete j entry = true ->
    aste_cpu entry < 2.
Proof.
  intros j entry H.
  unfold sched_trace_is_complete in H.
  peel_andb_left.
  apply Nat.eqb_eq in H.
  lia.
Qed.

Lemma sched_trace_is_stutter_cpu_in_range :
  forall entry,
    sched_trace_is_stutter entry = true ->
    aste_cpu entry < 2.
Proof.
  intros entry H.
  unfold sched_trace_is_stutter in H.
  peel_andb_left.
  apply Nat.eqb_eq in H.
  lia.
Qed.

Lemma sched_trace_step_start_cpu_in_range :
  forall summary entry st,
    sched_trace_step_start summary entry = Some st ->
    aste_cpu entry < 2.
Proof.
  intros summary entry st Hstep.
  unfold sched_trace_step_start in Hstep.
  destruct (atts_root_task summary) as [root|] eqn:Hroot; try discriminate.
  destruct (sched_trace_is_wakeup root entry) eqn:Hwakeup; inversion Hstep; subst.
  apply sched_trace_is_wakeup_cpu_in_range in Hwakeup.
  exact Hwakeup.
Qed.

Lemma sched_trace_step_after_start_cpu_in_range :
  forall summary st entry st',
    sched_trace_step_after_start summary st entry = Some st' ->
    aste_cpu entry < 2.
Proof.
  intros summary st entry st' Hstep.
  unfold sched_trace_step_after_start in Hstep.
  set (known := atts_known_tasks summary) in *.
  set (deps := atts_completion_deps summary) in *.
  set (try_wakeup_job :=
         fun j : JobId =>
           if sched_trace_is_wakeup j entry &&
              job_list_contains j known &&
              negb (job_list_contains j (astas_completed st))
           then Some st
           else None) in *.
  set (try_choose_job :=
         fun j : JobId =>
           if sched_trace_is_choose j entry &&
              job_list_contains j known &&
              negb (job_list_contains j (astas_completed st)) &&
              option_job_eqb (astas_selected st) None
           then Some
                  (mkAwkernelSchedTraceAcceptanceState
                     true
                     (Some j)
                     (astas_dispatched st)
                     (astas_completed st))
           else None) in *.
  set (try_dispatch_job :=
         fun j : JobId =>
           if sched_trace_is_dispatch j entry &&
              option_job_eqb (astas_selected st) (Some j)
           then Some
                  (mkAwkernelSchedTraceAcceptanceState
                     true None (add_job_once j (astas_dispatched st))
                     (astas_completed st))
           else None) in *.
  set (try_complete_job :=
         fun j : JobId =>
           if sched_trace_is_complete j entry &&
              job_list_contains j (astas_dispatched st) &&
              negb (job_list_contains j (astas_completed st)) &&
              all_dependencies_completed j deps (astas_completed st)
           then Some
                  (mkAwkernelSchedTraceAcceptanceState
                     true None (astas_dispatched st)
                     (add_job_once j (astas_completed st)))
           else None) in *.
  destruct (sched_trace_is_stutter entry) eqn:Hstutter.
  - inversion Hstep; subst.
    apply sched_trace_is_stutter_cpu_in_range in Hstutter.
    exact Hstutter.
  - destruct (first_some try_wakeup_job known) as [st1|] eqn:Hwakeups.
    + inversion Hstep; subst.
      apply first_some_some in Hwakeups.
      destruct Hwakeups as [j [_ Hj]].
      unfold try_wakeup_job in Hj.
      destruct
        (sched_trace_is_wakeup j entry &&
         job_list_contains j known &&
         negb (job_list_contains j (astas_completed st))) eqn:Hcond;
        simpl in Hj; try discriminate.
      inversion Hj; subst.
      apply Bool.andb_true_iff in Hcond as [Hwakeup _].
      apply Bool.andb_true_iff in Hwakeup as [Hwakeup _].
      eapply sched_trace_is_wakeup_cpu_in_range; eauto.
    + destruct (first_some try_choose_job known) as [st2|] eqn:Hchooses.
      * inversion Hstep; subst.
        apply first_some_some in Hchooses.
        destruct Hchooses as [j [_ Hj]].
        unfold try_choose_job in Hj.
        destruct
          (sched_trace_is_choose j entry &&
           job_list_contains j known &&
           negb (job_list_contains j (astas_completed st)) &&
           option_job_eqb (astas_selected st) None) eqn:Hcond;
          simpl in Hj; try discriminate.
        inversion Hj; subst.
        apply Bool.andb_true_iff in Hcond as [Hchoose _].
        apply Bool.andb_true_iff in Hchoose as [Hchoose _].
        apply Bool.andb_true_iff in Hchoose as [Hchoose _].
        eapply sched_trace_is_choose_cpu_in_range; eauto.
      * destruct (first_some try_dispatch_job known) as [st3|] eqn:Hdispatches.
        { inversion Hstep; subst.
          apply first_some_some in Hdispatches.
          destruct Hdispatches as [j [_ Hj]].
          unfold try_dispatch_job in Hj.
          destruct
            (sched_trace_is_dispatch j entry &&
             option_job_eqb (astas_selected st) (Some j)) eqn:Hcond;
            simpl in Hj; try discriminate.
          inversion Hj; subst.
          apply Bool.andb_true_iff in Hcond as [Hdispatch _].
          eapply sched_trace_is_dispatch_cpu_in_range; eauto. }
        { apply first_some_some in Hstep.
          destruct Hstep as [j [_ Hj]].
          unfold try_complete_job in Hj.
          destruct
            (sched_trace_is_complete j entry &&
             job_list_contains j (astas_dispatched st) &&
             negb (job_list_contains j (astas_completed st)) &&
             all_dependencies_completed j deps (astas_completed st)) eqn:Hcond;
            simpl in Hj; try discriminate.
          inversion Hj; subst.
          apply Bool.andb_true_iff in Hcond as [Hcomplete _].
          apply Bool.andb_true_iff in Hcomplete as [Hcomplete _].
          apply Bool.andb_true_iff in Hcomplete as [Hcomplete _].
          eapply sched_trace_is_complete_cpu_in_range; eauto. }
Qed.

Lemma sched_trace_step_cpu_in_range :
  forall summary st entry st',
    sched_trace_step summary st entry = Some st' ->
    aste_cpu entry < 2.
Proof.
  intros summary st entry st' Hstep.
  unfold sched_trace_step in Hstep.
  destruct (astas_started st) eqn:Hstarted.
  - eapply sched_trace_step_after_start_cpu_in_range; eauto.
  - eapply sched_trace_step_start_cpu_in_range; eauto.
Qed.

Lemma accept_sched_trace_from_cpus_in_range :
  forall summary st sched_trace,
    accept_sched_trace_from summary st sched_trace = true ->
    Forall (fun entry => aste_cpu entry < 2) sched_trace.
Proof.
  intros summary st sched_trace.
  revert st.
  induction sched_trace as [|entry sched_trace IH]; intros st Haccept; simpl in Haccept.
  - constructor.
  - destruct (sched_trace_step summary st entry) as [st'|] eqn:Hstep;
      try discriminate.
    constructor.
    + eapply sched_trace_step_cpu_in_range; eauto.
    + apply (IH st'). exact Haccept.
Qed.

Lemma accepted_workload_sched_trace_family_cpus_in_range :
  forall task_trace sched_trace,
    accepted_workload_sched_trace_family task_trace sched_trace ->
    Forall (fun entry => aste_cpu entry < 2) sched_trace.
Proof.
  intros task_trace sched_trace [summary [_ Hfamily]].
  unfold sched_trace_family_member in Hfamily.
  eapply accept_sched_trace_from_cpus_in_range; eauto.
Qed.
