From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.OSProjectionInterface.
From RocqSched Require Import Operational.Common.ConcreteExecution.
From RocqSched Require Import Operational.Common.Projection.
From RocqSched Require Import Operational.Common.ProjectionInvariants.

(* Canonical adapter-facing contract over a concrete labeled execution. The
   common layer keeps the concrete state type abstract and only exposes the
   projected scheduler view and the obligations needed to recover semantic
   schedule facts. *)
Record labeled_concrete_projection_sound
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteProjectionSound {
    lcps_release_sound :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        released jobs j t;
    lcps_completion_sound :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        ~ completed
            jobs
            m
            (project_schedule (osl_to_op_trace P (lce_trace ex)))
            j t;
    lcps_block_sound :
      forall t c j,
        c < m ->
        op_current
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t))
          c = Some j ->
        ~ blocked jobs j t;
  }.

Record labeled_concrete_multicore_projection_sound
    {CState : Type}
    {P : OSLabeledProjection CState}
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat)
    (ex : labeled_concrete_execution P m) : Prop :=
  mkLabeledConcreteMulticoreProjectionSound {
    lcmps_projection_sound :
      labeled_concrete_projection_sound jobs m ex;
    lcmps_idle_outside :
      forall t,
        op_idle_outside_range
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t));
    lcmps_placement :
      forall t,
        op_respects_admissibility
          adm
          m
          (os_to_op_state (osl_to_os_projection P) (lce_trace ex t));
  }.

Record os_multicore_adapter_contract
    {CState : Type}
    (P : OSLabeledProjection CState)
    (jobs : JobId -> Job)
    (adm : admissible_cpu)
    (m : nat) : Type :=
  mkOSMulticoreAdapterContract {
    oac_execution : labeled_concrete_execution P m;
    oac_sound :
      labeled_concrete_multicore_projection_sound jobs adm m oac_execution;
  }.

Arguments lcps_release_sound
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcps_completion_sound
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcps_block_sound
  {CState P jobs m ex} _ _ _ _ _ _.
Arguments lcmps_projection_sound
  {CState P jobs adm m ex} _.
Arguments lcmps_idle_outside
  {CState P jobs adm m ex} _ _.
Arguments lcmps_placement
  {CState P jobs adm m ex} _ _.
Arguments oac_execution
  {CState P jobs adm m} _.
Arguments oac_sound
  {CState P jobs adm m} _.
