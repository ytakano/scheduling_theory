From Stdlib Require Import List Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.SchedulerBridge.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.TopMSchedulerBridge.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.PlacementFacts.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.LabeledExecution.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.DelayModel.
From RocqSched Require Import Operational.Common.DelayBudget.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionLemmas.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Import Operational.Common.OSLocalAdapterContract.
From RocqSched Require Import Operational.Common.OSAdapterContract.
From RocqSched Require Import Refinement.BoundedDelayRefinement.
Import ListNotations.

Lemma local_labeled_concrete_projection_sound_to_global :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_projection_sound jobs m ex ->
    labeled_concrete_projection_sound jobs m ex.
Proof.
  intros CState P jobs m ex Hlocal.
  constructor.
  - intros t.
    induction t as [|t IH]; intros c j Hlt Hrun.
    + exact (llcps_init_release Hlocal c j Hlt Hrun).
    + destruct (llcps_current_origin Hlocal t c j Hlt Hrun) as [Hprev | [Hdispatch | Hpreempt]].
      * unfold released in *.
        specialize (IH c j Hlt Hprev).
        lia.
      * exact (llcps_dispatch_release Hlocal t c j Hlt Hdispatch).
      * destruct Hpreempt as [old Hpreempt].
        exact (llcps_preempt_release Hlocal t c old j Hlt Hpreempt).
  - intros t.
    induction t as [|t IH]; intros c j Hlt Hrun.
    + exact (llcps_init_completion Hlocal c j Hlt Hrun).
    + destruct (llcps_current_origin Hlocal t c j Hlt Hrun) as [Hprev | [Hdispatch | Hpreempt]].
      * exact (llcps_persistent_completion Hlocal t c j Hlt Hprev Hrun).
      * exact (llcps_dispatch_completion Hlocal t c j Hlt Hdispatch).
      * destruct Hpreempt as [old Hpreempt].
        exact (llcps_preempt_completion Hlocal t c old j Hlt Hpreempt).
Qed.

Lemma local_labeled_concrete_multicore_projection_sound_to_global :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    local_labeled_concrete_multicore_projection_sound jobs adm m ex ->
    labeled_concrete_multicore_projection_sound jobs adm m ex.
Proof.
  intros CState P jobs adm m ex Hlocal.
  constructor.
  - apply local_labeled_concrete_projection_sound_to_global.
    exact (llcmps_projection_sound Hlocal).
  - exact (llcmps_idle_outside Hlocal).
  - exact (llcmps_placement Hlocal).
Qed.

Definition os_local_multicore_adapter_contract_to_global
    {CState : Type}
    {P : OSLabeledProjection CState}
    {jobs : JobId -> Job}
    {adm : admissible_cpu}
    {m : nat}
    (C : os_local_multicore_adapter_contract P jobs adm m)
  : os_multicore_adapter_contract P jobs adm m :=
  @mkOSMulticoreAdapterContract
    CState
    P
    jobs
    adm
    m
    (olac_execution C)
    (local_labeled_concrete_multicore_projection_sound_to_global
       CState
       P
       jobs
       adm
       m
       (olac_execution C)
       (olac_sound C)).

Lemma local_labeled_concrete_projection_sound_request_sets_need_resched :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m) t c
         (Hlocal : local_labeled_concrete_projection_sound jobs m ex),
    c < m ->
    os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvRequestResched c ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
      c = true.
Proof.
  intros CState P jobs m ex t c Hlocal Hlt Hreq.
  exact (llcps_request_sets_need_resched Hlocal t c Hlt Hreq).
Qed.

Lemma local_labeled_concrete_projection_sound_handle_sets_need_resched :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m) t c
         (Hlocal : local_labeled_concrete_projection_sound jobs m ex),
    c < m ->
    os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvHandleResched c ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
      c = true.
Proof.
  intros CState P jobs m ex t c Hlocal Hlt Hhandle.
  exact (llcps_handle_sets_need_resched Hlocal t c Hlt Hhandle).
Qed.

Lemma local_labeled_concrete_projection_sound_choose_sets_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m) t c j
         (Hlocal : local_labeled_concrete_projection_sound jobs m ex),
    c < m ->
    os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
      c = Some j.
Proof.
  intros CState P jobs m ex t c j Hlocal Hlt Hchoose.
  exact (llcps_choose_sets_dispatch_target Hlocal t c j Hlt Hchoose).
Qed.

Lemma local_labeled_concrete_projection_sound_choose_from_runnable :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m) t c j
         (Hlocal : local_labeled_concrete_projection_sound jobs m ex),
    c < m ->
    os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
    In j
       (op_runnable
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))).
Proof.
  intros CState P jobs m ex t c j Hlocal Hlt Hchoose.
  exact (llcps_choose_from_runnable Hlocal t c j Hlt Hchoose).
Qed.

Lemma os_local_multicore_adapter_contract_handle_sets_need_resched :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvHandleResched c ->
    op_need_resched
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = true.
Proof.
  intros CState P jobs adm m C t c Hlt Hhandle.
  eapply local_labeled_concrete_projection_sound_handle_sets_need_resched
    with (jobs := jobs) (ex := olac_execution C) (t := t) (c := c).
  - exact (llcmps_projection_sound (olac_sound C)).
  - exact Hlt.
  - exact Hhandle.
Qed.

Lemma os_local_multicore_adapter_contract_choose_sets_dispatch_target :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvChoose c j ->
    op_dispatch_target
      (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) (S t)))
      c = Some j.
Proof.
  intros CState P jobs adm m C t c j Hlt Hchoose.
  eapply local_labeled_concrete_projection_sound_choose_sets_dispatch_target
    with (jobs := jobs) (ex := olac_execution C) (t := t) (c := c) (j := j).
  - exact (llcmps_projection_sound (olac_sound C)).
  - exact Hlt.
  - exact Hchoose.
Qed.

Lemma os_local_multicore_adapter_contract_choose_from_runnable :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m) t c j,
    c < m ->
    os_step_label P (lce_trace (olac_execution C) t) (lce_trace (olac_execution C) (S t)) =
    EvChoose c j ->
    In j
       (op_runnable
          (os_to_op_state (osl_to_os_projection P) (lce_trace (olac_execution C) t))).
Proof.
  intros CState P jobs adm m C t c j Hlt Hchoose.
  eapply local_labeled_concrete_projection_sound_choose_from_runnable
    with (jobs := jobs) (ex := olac_execution C) (t := t) (c := c) (j := j).
  - exact (llcmps_projection_sound (olac_sound C)).
  - exact Hlt.
  - exact Hchoose.
Qed.

Lemma labeled_concrete_projection_sound_to_labeled_execution :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_projection_sound jobs m ex ->
    labeled_execution_projection_sound jobs m (concrete_to_labeled_execution ex).
Proof.
  intros CState P jobs m ex Hsound.
  constructor.
  - intros t c j Hlt Hrun.
    exact (lcps_release_sound Hsound t c j Hlt Hrun).
  - intros t c j Hlt Hrun.
    exact (lcps_completion_sound Hsound t c j Hlt Hrun).
Qed.

Lemma labeled_concrete_projection_sound_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState) jobs m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_projection_sound jobs m ex ->
    valid_schedule
      jobs
      m
      (project_schedule (lex_trace (concrete_to_labeled_execution ex))).
Proof.
  intros CState P jobs m ex Hsound.
  apply labeled_execution_projection_sound_implies_valid_schedule.
  apply labeled_concrete_projection_sound_to_labeled_execution.
  exact Hsound.
Qed.

Lemma labeled_concrete_multicore_projection_sound_to_labeled_execution :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_multicore_projection_sound jobs adm m ex ->
    labeled_execution_multicore_projection_sound
      jobs adm m (concrete_to_labeled_execution ex).
Proof.
  intros CState P jobs adm m ex Hsound.
  constructor.
  - apply labeled_concrete_projection_sound_to_labeled_execution.
    exact (lcmps_projection_sound Hsound).
  - intros t.
    exact (lcmps_idle_outside Hsound t).
  - intros t.
    exact (lcmps_placement Hsound t).
Qed.

Lemma labeled_concrete_multicore_projection_sound_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_multicore_projection_sound jobs adm m ex ->
    valid_schedule
      jobs
      m
      (project_schedule (lex_trace (concrete_to_labeled_execution ex))).
Proof.
  intros CState P jobs adm m ex Hsound.
  apply labeled_concrete_projection_sound_implies_valid_schedule.
  exact (lcmps_projection_sound Hsound).
Qed.

Lemma labeled_concrete_multicore_projection_sound_implies_semantic_validity :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_multicore_projection_sound jobs adm m ex ->
    multicore_semantic_validity
      jobs
      m
      (project_schedule (lex_trace (concrete_to_labeled_execution ex))).
Proof.
  intros CState P jobs adm m ex Hsound.
  apply labeled_execution_multicore_projection_sound_implies_semantic_validity
    with (adm := adm).
  apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
  exact Hsound.
Qed.

Lemma labeled_concrete_multicore_projection_sound_implies_placement :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (ex : labeled_concrete_execution P m),
    labeled_concrete_multicore_projection_sound jobs adm m ex ->
    schedule_respects_admissibility
      adm
      m
      (project_schedule (lex_trace (concrete_to_labeled_execution ex))).
Proof.
  intros CState P jobs adm m ex Hsound.
  apply labeled_execution_multicore_projection_sound_implies_placement
    with (jobs := jobs).
  apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
  exact Hsound.
Qed.

Record os_delay_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSDelayAdapterContract {
    odac_base : os_multicore_adapter_contract P jobs adm m;
    odac_ideal_schedule : Schedule;
    odac_delay_bounds : op_delay_bounds;
    odac_delay_sources : DelayTrace;
    odac_delta : nat;
    odac_ideal_valid :
      multicore_semantic_validity jobs m odac_ideal_schedule;
    odac_default_sources_covered :
      forall t src,
        In src
           (default_event_delay_sources
              (lex_event
                 (concrete_to_labeled_execution (oac_execution odac_base)) t)) ->
        In src (odac_delay_sources t);
    odac_budget_within_delta :
      forall t,
        delay_budget_le
          odac_delay_bounds
          odac_delay_sources
          0
          t
          odac_delta;
    odac_service_lag :
      service_lag_le
        m
        odac_ideal_schedule
        (labeled_actual_schedule
           (concrete_to_labeled_execution (oac_execution odac_base)))
        odac_delta;
  }.

Record os_delay_top_m_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (spec : GenericTopMSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSDelayTopMAdapterContract {
    odtac_base : os_multicore_adapter_contract P jobs adm m;
    odtac_ideal_schedule : Schedule;
    odtac_delay_bounds : op_delay_bounds;
    odtac_delay_sources : DelayTrace;
    odtac_delta : nat;
    odtac_ideal_top_m :
      scheduler_rel
        (top_m_algorithm_schedule spec candidates_of)
        jobs m odtac_ideal_schedule;
    odtac_default_sources_covered :
      forall t src,
        In src
           (default_event_delay_sources
              (lex_event
                 (concrete_to_labeled_execution (oac_execution odtac_base)) t)) ->
        In src (odtac_delay_sources t);
    odtac_budget_within_delta :
      forall t,
        delay_budget_le
          odtac_delay_bounds
          odtac_delay_sources
          0
          t
          odtac_delta;
    odtac_service_lag :
      service_lag_le
        m
        odtac_ideal_schedule
        (labeled_actual_schedule
           (concrete_to_labeled_execution (oac_execution odtac_base)))
        odtac_delta;
  }.

Arguments odac_base {CState P jobs adm m} _.
Arguments odac_ideal_schedule {CState P jobs adm m} _.
Arguments odac_delay_bounds {CState P jobs adm m} _.
Arguments odac_delay_sources {CState P jobs adm m} _ _.
Arguments odac_delta {CState P jobs adm m} _.
Arguments odac_ideal_valid {CState P jobs adm m} _.
Arguments odtac_base {CState P spec candidates_of jobs adm m} _.
Arguments odtac_ideal_schedule {CState P spec candidates_of jobs adm m} _.
Arguments odtac_delay_bounds {CState P spec candidates_of jobs adm m} _.
Arguments odtac_delay_sources {CState P spec candidates_of jobs adm m} _ _.
Arguments odtac_delta {CState P spec candidates_of jobs adm m} _.
Arguments odtac_ideal_top_m {CState P spec candidates_of jobs adm m} _.

Lemma os_multicore_adapter_contract_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_multicore_adapter_contract P jobs adm m),
    valid_schedule
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (oac_execution C)))).
Proof.
  intros CState P jobs adm m [ex Hsound].
  apply labeled_concrete_multicore_projection_sound_implies_valid_schedule
    with (adm := adm).
  exact Hsound.
Qed.

Lemma os_local_multicore_adapter_contract_implies_valid_schedule :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m),
    valid_schedule
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros CState P jobs adm m C.
  change
    (valid_schedule
       jobs
       m
       (project_schedule
          (lex_trace
             (concrete_to_labeled_execution
                (oac_execution (os_local_multicore_adapter_contract_to_global C)))))).
  apply os_multicore_adapter_contract_implies_valid_schedule.
Qed.

Lemma os_multicore_adapter_contract_implies_semantic_validity :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_multicore_adapter_contract P jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (oac_execution C)))).
Proof.
  intros CState P jobs adm m [ex Hsound].
  apply labeled_concrete_multicore_projection_sound_implies_semantic_validity
    with (adm := adm).
  exact Hsound.
Qed.

Lemma os_local_multicore_adapter_contract_implies_semantic_validity :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m),
    multicore_semantic_validity
      jobs
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros CState P jobs adm m C.
  change
    (multicore_semantic_validity
       jobs
       m
       (project_schedule
          (lex_trace
             (concrete_to_labeled_execution
                (oac_execution (os_local_multicore_adapter_contract_to_global C)))))).
  apply os_multicore_adapter_contract_implies_semantic_validity.
Qed.

Lemma os_multicore_adapter_contract_implies_placement :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_multicore_adapter_contract P jobs adm m),
    schedule_respects_admissibility
      adm
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (oac_execution C)))).
Proof.
  intros CState P jobs adm m [ex Hsound].
  apply labeled_concrete_multicore_projection_sound_implies_placement
    with (jobs := jobs).
  exact Hsound.
Qed.

Lemma os_local_multicore_adapter_contract_implies_placement :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_local_multicore_adapter_contract P jobs adm m),
    schedule_respects_admissibility
      adm
      m
      (project_schedule
         (lex_trace (concrete_to_labeled_execution (olac_execution C)))).
Proof.
  intros CState P jobs adm m C.
  change
    (schedule_respects_admissibility
       adm
       m
       (project_schedule
          (lex_trace
             (concrete_to_labeled_execution
                (oac_execution (os_local_multicore_adapter_contract_to_global C)))))).
  apply os_multicore_adapter_contract_implies_placement.
Qed.

Lemma os_delay_adapter_contract_implies_bounded_delay_refinement :
  forall CState (P : OSLabeledProjection CState) jobs adm m
         (C : os_delay_adapter_contract P jobs adm m),
    let ex := @oac_execution CState P jobs adm m (odac_base C) in
    bounded_delay_projection_refinement
      jobs
      adm
      m
      (concrete_to_labeled_execution ex)
      (odac_ideal_schedule C)
      (odac_delay_bounds C)
      (odac_delay_sources C)
      (odac_delta C).
Proof.
  intros CState P jobs adm m C.
  destruct C as [base ideal bounds sources delta Hvalid Hcovered Hbudget Hlag].
  destruct base as [ex Hsound].
  apply mk_bounded_delay_projection_refinement.
  - apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
    exact Hsound.
  - exact Hvalid.
  - exact Hcovered.
  - exact Hbudget.
  - exact Hlag.
Qed.

Lemma os_delay_top_m_adapter_contract_implies_bounded_delay_top_m_refinement :
  forall CState (P : OSLabeledProjection CState)
         spec candidates_of jobs adm m
         (C : os_delay_top_m_adapter_contract P spec candidates_of jobs adm m),
    let ex := @oac_execution CState P jobs adm m (odtac_base C) in
    bounded_delay_top_m_projection_refinement
      spec
      candidates_of
      jobs
      adm
      m
      (concrete_to_labeled_execution ex)
      (odtac_ideal_schedule C)
      (odtac_delay_bounds C)
      (odtac_delay_sources C)
      (odtac_delta C).
Proof.
  intros CState P spec candidates_of jobs adm m C.
  destruct C as [base ideal bounds sources delta Htopm Hcovered Hbudget Hlag].
  destruct base as [ex Hsound].
  apply mk_bounded_delay_top_m_projection_refinement.
  - apply labeled_concrete_multicore_projection_sound_to_labeled_execution.
    exact Hsound.
  - exact Htopm.
  - exact Hcovered.
  - exact Hbudget.
  - exact Hlag.
Qed.
