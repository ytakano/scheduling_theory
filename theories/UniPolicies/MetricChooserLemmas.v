From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.SchedulePrefix.
Require Import SchedulingAlgorithmInterface.
Require Import SchedulingAlgorithmSchedulerBridge.
Require Import UniPolicies.MetricChooser.
Import ListNotations.

(* Common lemmas for metric-based scheduling algorithms (EDF, LLF, ...). *)

Lemma min_metric_job_ext :
  forall metric1 metric2 l,
    (forall j, In j l -> metric1 j = metric2 j) ->
    min_metric_job metric1 l = min_metric_job metric2 l.
Proof.
  intros metric1 metric2 l.
  induction l as [|j rest IH]; intros Hext; simpl.
  - reflexivity.
  - rewrite IH.
    2:{
      intros j' Hin.
      apply Hext.
      right. exact Hin.
    }
    destruct (min_metric_job metric2 rest) as [j'|] eqn:Hrest.
    + rewrite <- (Hext j (or_introl eq_refl)).
      rewrite <- (Hext j' (or_intror (min_metric_job_in metric2 rest j' Hrest))).
      reflexivity.
    + reflexivity.
Qed.

Lemma candidates_of_agrees_before :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs s1 s2 t,
    agrees_before s1 s2 t ->
    candidates_of jobs 1 s1 t = candidates_of jobs 1 s2 t.
Proof.
  intros J candidates_of cand_spec jobs s1 s2 t Hagree.
  destruct cand_spec as [_ _ Hpx].
  exact (Hpx jobs 1 s1 s2 t Hagree).
Qed.
