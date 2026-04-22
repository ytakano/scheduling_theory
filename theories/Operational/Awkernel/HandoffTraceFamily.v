From Stdlib Require Import List String Bool Arith Arith.PeanoNat Lia Logic.FunctionalExtensionality.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Awkernel.MinimalProjection.
From RocqSched Require Import Operational.Awkernel.BaselineTrace.
From RocqSched Require Import Operational.Awkernel.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.GeneratedHandoffTraceArtifact.
From RocqSched Require Import Operational.Awkernel.HandoffTrace.
Import ListNotations.

Section AwkernelHandoffTraceFamily.

  Definition op_event_eqb (x y : OpEvent) : bool :=
    match x, y with
    | EvWakeup j1, EvWakeup j2 => Nat.eqb j1 j2
    | EvBlock j1, EvBlock j2 => Nat.eqb j1 j2
    | EvComplete j1, EvComplete j2 => Nat.eqb j1 j2
    | EvRequestResched c1, EvRequestResched c2 => Nat.eqb c1 c2
    | EvHandleResched c1, EvHandleResched c2 => Nat.eqb c1 c2
    | EvChoose c1 j1, EvChoose c2 j2 => Nat.eqb c1 c2 && Nat.eqb j1 j2
    | EvDispatch c1 j1, EvDispatch c2 j2 => Nat.eqb c1 c2 && Nat.eqb j1 j2
    | EvPreempt c1 old1 new1, EvPreempt c2 old2 new2 =>
        Nat.eqb c1 c2 && Nat.eqb old1 old2 && Nat.eqb new1 new2
    | EvStutter, EvStutter => true
    | EvTick, EvTick => true
    | _, _ => false
    end.

  Lemma op_event_eqb_eq :
    forall x y,
      op_event_eqb x y = true ->
      x = y.
  Proof.
    intros x y.
    destruct x, y; simpl; try discriminate; intro H.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
      subst. reflexivity.
    - apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
      subst. reflexivity.
    - repeat rewrite andb_true_iff in H.
      destruct H as [[H1 H2] H3].
      apply Nat.eqb_eq in H1.
      apply Nat.eqb_eq in H2.
      apply Nat.eqb_eq in H3.
      subst. reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Definition awk_handoff_row_wakeup : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 0 (EvWakeup 1) None [1] false None.

  Definition awk_handoff_row_request_resched : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvRequestResched 1) None [1] true None.

  Definition awk_handoff_row_handle_resched : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvHandleResched 1) None [1] true None.

  Definition awk_handoff_row_choose : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvChoose 1 1) None [1] true (Some 1).

  Definition awk_handoff_row_dispatch : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvDispatch 1 1) (Some 1) [] false None.

  Definition awk_handoff_row_complete : AwkernelCapturedRow :=
    mkAwkernelCapturedRow 1 (EvComplete 1) None [] true None.

  Definition awk_handoff_seed_rows : list AwkernelCapturedRow :=
    [ awk_handoff_row_wakeup
    ; awk_handoff_row_request_resched
    ; awk_handoff_row_handle_resched
    ; awk_handoff_row_choose
    ; awk_handoff_row_dispatch
    ; awk_handoff_row_complete
    ].

  Lemma awk_handoff_seed_rows_eq_generated :
    awk_handoff_seed_rows = awk_generated_handoff_rows.
  Proof.
    reflexivity.
  Qed.

  Inductive awk_handoff_row_step
    : AwkernelHandoffState -> AwkernelCapturedRow -> AwkernelHandoffState -> Prop :=
  | awk_handoff_row_step_wakeup :
      awk_handoff_row_step
        awk_handoff_state0
        awk_handoff_row_wakeup
        awk_handoff_state1
  | awk_handoff_row_step_request_resched :
      awk_handoff_row_step
        awk_handoff_state1
        awk_handoff_row_request_resched
        awk_handoff_state2
  | awk_handoff_row_step_handle_resched :
      awk_handoff_row_step
        awk_handoff_state2
        awk_handoff_row_handle_resched
        awk_handoff_state3
  | awk_handoff_row_step_choose :
      awk_handoff_row_step
        awk_handoff_state3
        awk_handoff_row_choose
        awk_handoff_state4
  | awk_handoff_row_step_dispatch :
      awk_handoff_row_step
        awk_handoff_state4
        awk_handoff_row_dispatch
        awk_handoff_state5
  | awk_handoff_row_step_complete :
      awk_handoff_row_step
        awk_handoff_state5
        awk_handoff_row_complete
        awk_handoff_state6
  | awk_handoff_row_step_stutter :
      forall st row,
        acr_event row = EvStutter ->
        awk_row_to_state row = awk_handoff_visible st ->
        awk_handoff_row_step
          st
          row
          (mkAwkernelHandoffState (awk_handoff_visible st) (awk_handoff_phase st)).

  Inductive awk_handoff_row_generation_from
    : AwkernelHandoffState ->
      list AwkernelCapturedRow ->
      list AwkernelHandoffState -> Prop :=
  | awk_handoff_row_generation_nil :
      forall st,
        awk_handoff_row_generation_from st [] []
  | awk_handoff_row_generation_cons :
      forall st row st' rows states,
        awk_handoff_row_step st row st' ->
        awk_handoff_row_generation_from st' rows states ->
        awk_handoff_row_generation_from st (row :: rows) (st' :: states).

  Definition awk_handoff_row_generation
      (rows : list AwkernelCapturedRow)
      (states : list AwkernelHandoffState) : Prop :=
    awk_handoff_row_generation_from awk_handoff_state0 rows states.

  Definition awk_handoff_generated_final_state_from
      (st : AwkernelHandoffState)
      (states : list AwkernelHandoffState) : AwkernelHandoffState :=
    last states st.

  Definition awk_handoff_generated_trace_from
      (st : AwkernelHandoffState)
      (states : list AwkernelHandoffState)
      (t : Time) : AwkernelHandoffState :=
    match t with
    | 0 => st
    | S t' => nth t' states (awk_handoff_generated_final_state_from st states)
    end.

  Definition awk_handoff_generated_trace
      (states : list AwkernelHandoffState)
      (t : Time) : AwkernelHandoffState :=
    awk_handoff_generated_trace_from awk_handoff_state0 states t.

  Definition awk_row_matches_visible
      (row : AwkernelCapturedRow)
      (vis : AwkernelState) : Prop :=
    awk_current (awk_row_to_state row) 0 = awk_current vis 0 /\
    awk_current (awk_row_to_state row) 1 = awk_current vis 1 /\
    awk_runnable (awk_row_to_state row) = awk_runnable vis /\
    awk_need_resched (awk_row_to_state row) 0 = awk_need_resched vis 0 /\
    awk_need_resched (awk_row_to_state row) 1 = awk_need_resched vis 1 /\
    awk_dispatch_target (awk_row_to_state row) 0 = awk_dispatch_target vis 0 /\
    awk_dispatch_target (awk_row_to_state row) 1 = awk_dispatch_target vis 1.

  Definition option_job_eqb
      (x y : option JobId) : bool :=
    match x, y with
    | Some j1, Some j2 => Nat.eqb j1 j2
    | None, None => true
    | _, _ => false
    end.

  Fixpoint job_list_eqb (xs ys : list JobId) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => Nat.eqb x y && job_list_eqb xs' ys'
    | _, _ => false
    end.

  Definition captured_row_eqb
      (x y : AwkernelCapturedRow) : bool :=
    Nat.eqb (acr_cpu x) (acr_cpu y) &&
    op_event_eqb (acr_event x) (acr_event y) &&
    option_job_eqb (acr_current x) (acr_current y) &&
    job_list_eqb (acr_runnable x) (acr_runnable y) &&
    Bool.eqb (acr_need_resched x) (acr_need_resched y) &&
    option_job_eqb (acr_dispatch_target x) (acr_dispatch_target y).

  Definition awk_row_matches_visibleb
      (row : AwkernelCapturedRow)
      (vis : AwkernelState) : bool :=
    option_job_eqb
      (awk_current (awk_row_to_state row) 0)
      (awk_current vis 0) &&
    option_job_eqb
      (awk_current (awk_row_to_state row) 1)
      (awk_current vis 1) &&
    job_list_eqb
      (awk_runnable (awk_row_to_state row))
      (awk_runnable vis) &&
    Bool.eqb
      (awk_need_resched (awk_row_to_state row) 0)
      (awk_need_resched vis 0) &&
    Bool.eqb
      (awk_need_resched (awk_row_to_state row) 1)
      (awk_need_resched vis 1) &&
    option_job_eqb
      (awk_dispatch_target (awk_row_to_state row) 0)
      (awk_dispatch_target vis 0) &&
    option_job_eqb
      (awk_dispatch_target (awk_row_to_state row) 1)
      (awk_dispatch_target vis 1).

  Lemma option_job_eqb_eq :
    forall x y,
      option_job_eqb x y = true ->
      x = y.
  Proof.
    destruct x as [j|], y as [j'|]; simpl; try discriminate; intros H.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - reflexivity.
  Qed.

  Lemma job_list_eqb_eq :
    forall xs ys,
      job_list_eqb xs ys = true ->
      xs = ys.
  Proof.
    induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; try discriminate; intros H.
    - reflexivity.
    - apply andb_true_iff in H as [Hxy Hrest].
      apply Nat.eqb_eq in Hxy.
      apply IH in Hrest.
      subst. reflexivity.
  Qed.

  Lemma captured_row_eqb_eq :
    forall x y,
      captured_row_eqb x y = true ->
      x = y.
  Proof.
    intros [cpu1 event1 current1 runnable1 need1 dispatch1]
           [cpu2 event2 current2 runnable2 need2 dispatch2].
    unfold captured_row_eqb; simpl.
    intro H.
    apply andb_true_iff in H as [Habcde Hdispatch].
    apply andb_true_iff in Habcde as [Habcd Hneed].
    apply andb_true_iff in Habcd as [Habc Hrunnable].
    apply andb_true_iff in Habc as [Hab Hcurrent].
    apply andb_true_iff in Hab as [Hcpu Hevent].
    apply Nat.eqb_eq in Hcpu.
    apply op_event_eqb_eq in Hevent.
    apply option_job_eqb_eq in Hcurrent.
    apply job_list_eqb_eq in Hrunnable.
    destruct need1, need2; simpl in Hneed; try discriminate.
    - apply option_job_eqb_eq in Hdispatch. subst. reflexivity.
    - apply option_job_eqb_eq in Hdispatch. subst. reflexivity.
  Qed.

  Lemma awk_row_matches_visibleb_sound :
    forall row vis,
      awk_row_matches_visibleb row vis = true ->
      awk_row_matches_visible row vis.
  Proof.
    intros row vis.
    unfold awk_row_matches_visibleb, awk_row_matches_visible.
    intros H.
    repeat rewrite andb_true_iff in H.
    destruct H as [[[[[[Hcur0 Hcur1] Hrunnable] Hneed0] Hneed1] Hdispatch0] Hdispatch1].
    repeat split.
    - apply option_job_eqb_eq. exact Hcur0.
    - apply option_job_eqb_eq. exact Hcur1.
    - apply job_list_eqb_eq. exact Hrunnable.
    - apply Bool.eqb_true_iff. exact Hneed0.
    - apply Bool.eqb_true_iff. exact Hneed1.
    - apply option_job_eqb_eq. exact Hdispatch0.
    - apply option_job_eqb_eq. exact Hdispatch1.
  Qed.

  Definition awk_handoff_row_step_next
      (st : AwkernelHandoffState)
      (row : AwkernelCapturedRow) : option AwkernelHandoffState :=
    if captured_row_eqb row awk_handoff_row_wakeup then
      match awk_handoff_phase st with
      | 0 => Some awk_handoff_state1
      | _ => None
      end
    else if captured_row_eqb row awk_handoff_row_request_resched then
      match awk_handoff_phase st with
      | 1 => Some awk_handoff_state2
      | _ => None
      end
    else if captured_row_eqb row awk_handoff_row_handle_resched then
      match awk_handoff_phase st with
      | 2 => Some awk_handoff_state3
      | _ => None
      end
    else if captured_row_eqb row awk_handoff_row_choose then
      match awk_handoff_phase st with
      | 3 => Some awk_handoff_state4
      | _ => None
      end
    else if captured_row_eqb row awk_handoff_row_dispatch then
      match awk_handoff_phase st with
      | 4 => Some awk_handoff_state5
      | _ => None
      end
    else if captured_row_eqb row awk_handoff_row_complete then
      match awk_handoff_phase st with
      | 5 => Some awk_handoff_state6
      | _ => None
      end
    else
      None.

  Fixpoint awk_handoff_generate_post_states_from
      (st : AwkernelHandoffState)
      (rows : list AwkernelCapturedRow) : option (list AwkernelHandoffState) :=
    match rows with
    | [] => Some []
    | row :: rows' =>
        match awk_handoff_row_step_next st row with
        | None => None
        | Some st' =>
            match awk_handoff_generate_post_states_from st' rows' with
            | None => None
            | Some states => Some (st' :: states)
            end
        end
    end.

  Definition awk_handoff_generate_post_states
      (rows : list AwkernelCapturedRow) : option (list AwkernelHandoffState) :=
    awk_handoff_generate_post_states_from awk_handoff_state0 rows.

  Definition awk_handoff_check_rows
      (rows : list AwkernelCapturedRow) : option (list AwkernelHandoffState) :=
    awk_handoff_generate_post_states rows.

  Definition awk_handoff_rows_replay_trace
      (rows : list AwkernelCapturedRow)
      (t : Time) : AwkernelHandoffState :=
    match awk_handoff_check_rows rows with
    | Some states => awk_handoff_generated_trace states t
    | None => awk_handoff_state0
    end.

  Definition awk_handoff_accepts_rows
      (rows : list AwkernelCapturedRow) : bool :=
    match awk_handoff_check_rows rows with
    | Some _ => true
    | None => false
    end.

  Definition awk_handoff_seed_state (st : AwkernelHandoffState) : Prop :=
    st = awk_handoff_state0 \/
    st = awk_handoff_state1 \/
    st = awk_handoff_state2 \/
    st = awk_handoff_state3 \/
    st = awk_handoff_state4 \/
    st = awk_handoff_state5 \/
    st = awk_handoff_state6.

  Lemma awk_handoff_row_step_next_sound :
    forall st row st',
      awk_handoff_seed_state st ->
      awk_handoff_row_step_next st row = Some st' ->
      awk_handoff_row_step st row st'.
  Proof.
    intros st row st' Hseed Hnext.
    destruct Hseed as [Hseed0|[Hseed1|[Hseed2|[Hseed3|[Hseed4|[Hseed5|Hseed6]]]]]];
      subst st; unfold awk_handoff_row_step_next in Hnext; simpl in Hnext.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup.
      + apply captured_row_eqb_eq in Hwakeup. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_wakeup.
      + destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq.
      + apply captured_row_eqb_eq in Hreq. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_request_resched.
      + destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle.
      + apply captured_row_eqb_eq in Hhandle. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_handle_resched.
      + destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose.
      + apply captured_row_eqb_eq in Hchoose. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_choose.
      + destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
        destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch.
      + apply captured_row_eqb_eq in Hdispatch. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_dispatch.
      + destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete.
      + apply captured_row_eqb_eq in Hcomplete. subst row.
        inversion Hnext; subst st'. exact awk_handoff_row_step_complete.
      + discriminate.
    - destruct (captured_row_eqb row awk_handoff_row_wakeup) eqn:Hwakeup; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_request_resched) eqn:Hreq; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_handle_resched) eqn:Hhandle; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_choose) eqn:Hchoose; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_dispatch) eqn:Hdispatch; try discriminate.
      destruct (captured_row_eqb row awk_handoff_row_complete) eqn:Hcomplete; discriminate.
  Qed.

  Lemma awk_handoff_row_step_target_is_seed :
    forall st row st',
      awk_handoff_seed_state st ->
      awk_handoff_row_step st row st' ->
      awk_handoff_seed_state st'.
  Proof.
    intros st row st' Hseed Hstep.
    inversion Hstep; subst; unfold awk_handoff_seed_state in *; try tauto.
    destruct Hseed as [Hseed0|[Hseed1|[Hseed2|[Hseed3|[Hseed4|[Hseed5|Hseed6]]]]]];
      subst st; unfold awk_handoff_seed_state; firstorder.
  Qed.

  Lemma awk_handoff_check_rows_from_sound :
    forall st rows states,
      awk_handoff_seed_state st ->
      awk_handoff_generate_post_states_from st rows = Some states ->
      awk_handoff_row_generation_from st rows states.
  Proof.
    intros st rows states Hseed Hgen.
    revert st states Hseed Hgen.
    induction rows as [|row rows IH]; intros st states Hseed Hgen.
    - simpl in Hgen. inversion Hgen; subst. constructor.
    - simpl in Hgen.
      destruct (awk_handoff_row_step_next st row) as [st'|] eqn:Hstep; try discriminate.
      destruct (awk_handoff_generate_post_states_from st' rows) as [states'|] eqn:Hrest; try discriminate.
      inversion Hgen; subst states.
      pose proof (awk_handoff_row_step_next_sound st row st' Hseed Hstep) as Hstep_sound.
      econstructor.
      + exact Hstep_sound.
      + eapply IH.
        * eapply awk_handoff_row_step_target_is_seed; eauto.
        * exact Hrest.
  Qed.

  Lemma awk_handoff_check_rows_sound :
    forall rows states,
      awk_handoff_check_rows rows = Some states ->
      awk_handoff_row_generation rows states.
  Proof.
    intros rows states.
    unfold awk_handoff_check_rows, awk_handoff_generate_post_states, awk_handoff_row_generation.
    apply awk_handoff_check_rows_from_sound.
    unfold awk_handoff_seed_state. now left.
  Qed.

  Lemma awk_handoff_accepts_rows_sound :
    forall rows,
      awk_handoff_accepts_rows rows = true ->
      exists states, awk_handoff_row_generation rows states.
  Proof.
    intros rows.
    unfold awk_handoff_accepts_rows, awk_handoff_check_rows.
    destruct (awk_handoff_generate_post_states rows) as [states|] eqn:Hcheck; simpl; try discriminate.
    intro Haccept. exists states.
    now apply awk_handoff_check_rows_sound.
  Qed.

  Lemma awk_handoff_rows_replay_trace_of_checked_rows :
    forall rows states,
      awk_handoff_check_rows rows = Some states ->
      forall t,
        awk_handoff_rows_replay_trace rows t =
        awk_handoff_generated_trace states t.
  Proof.
    intros rows states Hcheck t.
    unfold awk_handoff_rows_replay_trace.
    now rewrite Hcheck.
  Qed.

  Lemma awk_handoff_accepts_rows_bridge :
    forall rows,
      awk_handoff_accepts_rows rows = true ->
      exists states,
        awk_handoff_check_rows rows = Some states /\
        awk_handoff_row_generation rows states /\
        forall t,
          awk_handoff_rows_replay_trace rows t =
          awk_handoff_generated_trace states t.
  Proof.
    intros rows Haccept.
    unfold awk_handoff_accepts_rows, awk_handoff_check_rows in Haccept.
    destruct (awk_handoff_generate_post_states rows) as [states|] eqn:Hcheck;
      simpl in Haccept; try discriminate.
    exists states.
    split.
    - exact Hcheck.
    - split.
      + now apply awk_handoff_check_rows_sound.
      + now apply awk_handoff_rows_replay_trace_of_checked_rows.
  Qed.

  Lemma awk_handoff_row_step_label :
    forall st row st',
      awk_handoff_row_step st row st' ->
      awk_handoff_labeler st st' = acr_event row.
  Proof.
    intros st row st' Hstep.
    inversion Hstep; subst; try reflexivity.
    unfold awk_handoff_labeler.
    destruct st as [vis ph].
    simpl in *.
    destruct ph as [|[|[|[|[|[|ph']]]]]]; rewrite H; reflexivity.
  Qed.

  Lemma awk_handoff_seed_rows_are_generated :
    awk_handoff_row_generation
      awk_handoff_seed_rows
      [ awk_handoff_state1
      ; awk_handoff_state2
      ; awk_handoff_state3
      ; awk_handoff_state4
      ; awk_handoff_state5
      ; awk_handoff_state6
      ].
  Proof.
    unfold awk_handoff_row_generation, awk_handoff_seed_rows.
    econstructor.
    - exact awk_handoff_row_step_wakeup.
    - econstructor.
      + exact awk_handoff_row_step_request_resched.
      + econstructor.
        * exact awk_handoff_row_step_handle_resched.
        * econstructor.
          -- exact awk_handoff_row_step_choose.
          -- econstructor.
             ++ exact awk_handoff_row_step_dispatch.
             ++ econstructor.
                ** exact awk_handoff_row_step_complete.
                ** constructor.
  Qed.

  Lemma awk_handoff_generated_rows_are_generated :
    awk_handoff_row_generation
      awk_generated_handoff_rows
      [ awk_handoff_state1
      ; awk_handoff_state2
      ; awk_handoff_state3
      ; awk_handoff_state4
      ; awk_handoff_state5
      ; awk_handoff_state6
      ].
  Proof.
    rewrite <- awk_handoff_seed_rows_eq_generated.
    exact awk_handoff_seed_rows_are_generated.
  Qed.

  Example awk_handoff_generated_rows_compute_post_states :
    awk_handoff_generate_post_states awk_generated_handoff_rows =
    Some
      [ awk_handoff_state1
      ; awk_handoff_state2
      ; awk_handoff_state3
      ; awk_handoff_state4
      ; awk_handoff_state5
      ; awk_handoff_state6
      ].
  Proof.
    cbv [awk_handoff_generate_post_states
         awk_handoff_generate_post_states_from
         awk_handoff_row_step_next
         captured_row_eqb
         op_event_eqb
         awk_generated_handoff_rows
         awk_handoff_row_wakeup
         awk_handoff_row_request_resched
         awk_handoff_row_handle_resched
         awk_handoff_row_choose
         awk_handoff_row_dispatch
         awk_handoff_row_complete].
    cbv [awk_row_matches_visibleb option_job_eqb job_list_eqb awk_row_to_state].
    reflexivity.
  Qed.

  Example awk_handoff_generated_rows_are_accepted :
    awk_handoff_accepts_rows awk_generated_handoff_rows = true.
  Proof.
    unfold awk_handoff_accepts_rows, awk_handoff_check_rows.
    rewrite awk_handoff_generated_rows_compute_post_states.
    reflexivity.
  Qed.

  Example awk_handoff_dispatch_only_is_rejected :
    awk_handoff_accepts_rows [awk_handoff_row_dispatch] = false.
  Proof.
    unfold awk_handoff_accepts_rows, awk_handoff_check_rows,
      awk_handoff_generate_post_states, awk_handoff_generate_post_states_from,
      awk_handoff_row_step_next, captured_row_eqb.
    simpl.
    reflexivity.
  Qed.

End AwkernelHandoffTraceFamily.
