From Stdlib Require Import List.
Import ListNotations.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionInvariants.

(* Local adapter-side contract over individual projected steps. This keeps the
   global projection packages reusable while letting concrete adapters justify
   the projection with event-local obligations. *)
Record local_labeled_concrete_projection_sound
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLocalLabeledConcreteProjectionSound {
    llcps_init_release :
      forall c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex 0))
          c = Some j ->
        released jobs j 0;
    llcps_init_completion :
      forall c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex 0))
          c = Some j ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            j 0;
    llcps_current_origin :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j \/
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j \/
        exists old,
          os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
          EvPreempt c old j;
    llcps_dispatch_release :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        released jobs j (S t);
    llcps_wakeup_release :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvWakeup j ->
        released jobs j (S t);
    llcps_persistent_completion :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            j (S t);
    llcps_request_sets_need_resched :
      forall t c,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvRequestResched c ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = true;
    llcps_handle_sets_need_resched :
      forall t c,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvHandleResched c ->
        op_need_resched
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = true;
    llcps_choose_sets_dispatch_target :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
        op_dispatch_target
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex (S t)))
          c = Some j;
    llcps_choose_from_runnable :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvChoose c j ->
        In j
           (op_runnable
              (os_to_op_state (osl_to_os_projection P) (lce_trace ex t)));
    llcps_dispatch_completion :
      forall t c j,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvDispatch c j ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            j (S t);
    llcps_complete_sets_completed :
      forall t j,
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) = EvComplete j ->
        completed
          jobs
          m
          (project_schedule (osl_to_op_trace P (lce_trace ex)))
          j (S t);
    llcps_preempt_release :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        released jobs new (S t);
    llcps_preempt_completion :
      forall t c old new,
        c < m ->
        os_step_label P (lce_trace ex t) (lce_trace ex (S t)) =
        EvPreempt c old new ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            new (S t);
  }.

Record local_labeled_concrete_multicore_projection_sound
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLocalLabeledConcreteMulticoreProjectionSound {
    llcmps_projection_sound :
      local_labeled_concrete_projection_sound jobs m ex;
    llcmps_idle_outside :
      forall t,
        op_idle_outside_range
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t));
    llcmps_placement :
      forall t,
        op_respects_admissibility
          adm
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t));
  }.

Record os_local_multicore_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSLocalMulticoreAdapterContract {
    olac_execution : labeled_concrete_execution P m;
    olac_sound :
      local_labeled_concrete_multicore_projection_sound jobs adm m olac_execution;
  }.

Arguments llcps_init_release
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_init_completion
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_current_origin
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments llcps_dispatch_release
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_wakeup_release
  {CState P jobs m ex} _ _ _.
Arguments llcps_persistent_completion
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments llcps_request_sets_need_resched
  {CState P jobs m ex} _ _ _ _.
Arguments llcps_handle_sets_need_resched
  {CState P jobs m ex} _ _ _ _.
Arguments llcps_choose_sets_dispatch_target
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_choose_from_runnable
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_dispatch_completion
  {CState P jobs m ex} _ _ _ _ _.
Arguments llcps_complete_sets_completed
  {CState P jobs m ex} _ _ _.
Arguments llcps_preempt_release
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments llcps_preempt_completion
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments llcmps_projection_sound
  {CState P jobs adm m ex} _.
Arguments llcmps_idle_outside
  {CState P jobs adm m ex} _ _.
Arguments llcmps_placement
  {CState P jobs adm m ex} _ _.
Arguments olac_execution
  {CState P jobs adm m} _.
Arguments olac_sound
  {CState P jobs adm m} _.
