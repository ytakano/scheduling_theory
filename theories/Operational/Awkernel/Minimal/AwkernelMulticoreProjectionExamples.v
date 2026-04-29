From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.Admissibility.
From RocqSched Require Import Multicore.Common.ValidityFacts.
From RocqSched Require Import Operational.Common.State.
From RocqSched Require Import Operational.Common.Invariants.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Common.ProjectionInvariants.
From RocqSched Require Import Operational.Common.ProjectionMulticoreValidity.
From RocqSched Require Import Operational.Awkernel.Minimal.MinimalProjection.
Import ListNotations.

(** Worked 2-CPU projection example for the Awkernel minimal adapter boundary. *)
Section AwkernelMulticoreProjectionExamples.

  Definition awk_example_job0 : Job := mkJob 0 0 0 3 5 (fun _ => false).
  Definition awk_example_job1 : Job := mkJob 1 0 0 2 4 (fun _ => false).

  Definition awk_example_jobs (j : JobId) : Job :=
    match j with
    | 0 => awk_example_job0
    | _ => awk_example_job1
    end.

  Definition awk_example_admissibility : admissible_cpu :=
    fun j c => j = c.

  Definition awk_state : AwkernelState :=
    mkAwkernelState (fun _ => None) [] (fun _ => false) (fun _ => None).

  Definition awk_trace (_ : Time) : AwkernelState := awk_state.

  Lemma awk_struct_inv :
    forall t, op_struct_inv 2 (awk_to_op_state (awk_trace t)).
  Proof.
    intros t.
    constructor.
      - intros j c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
        simpl in Hrun1.
        discriminate.
      - constructor.
    - intros c j Hrun Hin.
      simpl in Hin.
      contradiction.
      - intros j c1 c2 Hlt1 Hlt2 Ht1 Ht2.
        simpl in Ht1.
        discriminate.
      - intros c j Hlt Ht.
        simpl in Ht.
        discriminate.
  Qed.

  Definition awk_execution_ex : awk_execution 2 :=
    mkAwkExecution 2 awk_trace True (fun _ => ex_intro _ EvStutter (step_stutter _)) awk_struct_inv.

  Lemma awk_execution_projection_sound :
    awk_multicore_projection_sound awk_example_jobs awk_example_admissibility 2 awk_execution_ex.
  Proof.
    constructor.
    - constructor.
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state in Hrun.
        simpl in Hrun.
        discriminate.
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state in Hrun.
        simpl in Hrun.
        discriminate.
      + intros t c j Hlt Hrun.
        unfold awk_trace, awk_state, blocked in Hrun |- *.
        simpl in Hrun.
        discriminate.
    - intros t.
      unfold awk_trace, awk_state, awk_idle_outside_range, op_idle_outside_range.
      intros c Hge.
      reflexivity.
    - intros t c j Hlt Hrun.
      unfold awk_trace, awk_state, awk_respects_admissibility,
             op_respects_admissibility, awk_example_admissibility in *.
      simpl in Hrun.
      discriminate.
  Qed.

  Example awk_projection_has_multicore_semantic_validity :
    multicore_semantic_validity awk_example_jobs 2 (awk_project_schedule (awk_ex_trace awk_execution_ex)).
  Proof.
    eapply awk_multicore_projection_sound_implies_semantic_validity.
    exact awk_execution_projection_sound.
  Qed.

End AwkernelMulticoreProjectionExamples.
