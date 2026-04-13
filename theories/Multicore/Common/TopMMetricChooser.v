(* TopMMetricChooser.v
   Metric-based top-m chooser built on choose_min_metric.

   choose_top_m_by_metric k metric jobs m sched t candidates
     recursively picks the minimum-metric eligible candidate, removes it from
     the pool, and repeats up to k times.

   Proves the four structural properties required by GenericTopMSchedulingAlgorithm,
   then packages them into make_metric_top_m_algorithm.
*)

From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia ZArith.
From SchedulingTheory Require Import Foundation.Base.
From SchedulingTheory Require Import Semantics.Schedule.
From SchedulingTheory Require Import Abstractions.SchedulingAlgorithm.TopMInterface.
From SchedulingTheory Require Import Uniprocessor.Policies.Common.MetricChooser.
Import ListNotations.

(* ===== Core definition ===== *)

Fixpoint choose_top_m_by_metric
    (k : nat)
    (metric : JobId -> Z)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : list JobId :=
  match k with
  | 0 => []
  | S k' =>
      match choose_min_metric metric jobs m sched t candidates with
      | None   => []
      | Some j =>
          j :: choose_top_m_by_metric k' metric jobs m sched t
                 (List.remove Nat.eq_dec j candidates)
      end
  end.

(* ===== Expansion lemmas (expose the fixpoint step) ===== *)

Lemma choose_top_m_by_metric_Sn_some :
  forall k' metric jobs m sched t candidates best,
    choose_min_metric metric jobs m sched t candidates = Some best ->
    choose_top_m_by_metric (S k') metric jobs m sched t candidates =
      best :: choose_top_m_by_metric k' metric jobs m sched t
               (List.remove Nat.eq_dec best candidates).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma choose_top_m_by_metric_Sn_none :
  forall k' metric jobs m sched t candidates,
    choose_min_metric metric jobs m sched t candidates = None ->
    choose_top_m_by_metric (S k') metric jobs m sched t candidates = [].
Proof. intros. simpl. rewrite H. reflexivity. Qed.

(* ===== 1. Length bound ===== *)

Lemma choose_top_m_by_metric_length_le :
  forall k metric jobs m sched t candidates,
    length (choose_top_m_by_metric k metric jobs m sched t candidates) <= k.
Proof.
  induction k as [|k' IH]; intros.
  - simpl. lia.
  - simpl.
    destruct (choose_min_metric metric jobs m sched t candidates).
    + simpl. apply le_n_S. apply IH.
    + simpl. lia.
Qed.

(* ===== 2. In-candidates ===== *)

Lemma choose_top_m_by_metric_in_candidates :
  forall k metric jobs m sched t candidates j,
    In j (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    In j candidates.
Proof.
  induction k as [|k' IH]; intros.
  - simpl in H. contradiction.
  - simpl in H.
    destruct (choose_min_metric metric jobs m sched t candidates) as [best|] eqn:Hbest.
    + destruct H as [Hjbest | Hrest].
      * subst best. exact (choose_min_metric_in_candidates _ _ _ _ _ _ _ Hbest).
      * apply IH in Hrest.
        (* Hrest : In j (remove Nat.eq_dec best candidates)
           in_remove : A eq_dec l x y -> In x (remove y l) -> In x l /\ x <> y *)
        exact (proj1 (@in_remove _ Nat.eq_dec candidates j best Hrest)).
    + contradiction.
Qed.

(* ===== 3. Eligibility ===== *)

Lemma choose_top_m_by_metric_eligible :
  forall k metric jobs m sched t candidates j,
    In j (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    eligible jobs m sched j t.
Proof.
  induction k as [|k' IH]; intros.
  - simpl in H. contradiction.
  - simpl in H.
    destruct (choose_min_metric metric jobs m sched t candidates) as [best|] eqn:Hbest.
    + destruct H as [Hjbest | Hrest].
      * subst best. exact (choose_min_metric_eligible _ _ _ _ _ _ _ Hbest).
      * exact (IH _ _ _ _ _ (List.remove Nat.eq_dec best candidates) j Hrest).
    + contradiction.
Qed.

(* ===== 4. NoDup ===== *)

Lemma choose_top_m_by_metric_nodup :
  forall k metric jobs m sched t candidates,
    NoDup (choose_top_m_by_metric k metric jobs m sched t candidates).
Proof.
  induction k as [|k' IH]; intros.
  - constructor.
  - simpl.
    destruct (choose_min_metric metric jobs m sched t candidates) as [best|] eqn:Hbest.
    + apply NoDup_cons.
      * intros Hin.
        apply choose_top_m_by_metric_in_candidates in Hin.
        (* Hin : In best (remove Nat.eq_dec best candidates)
           in_remove : In best candidates /\ best <> best *)
        exact ((proj2 (@in_remove _ Nat.eq_dec candidates best best Hin)) eq_refl).
      * apply IH.
    + constructor.
Qed.

(* ===== 5. Completeness if room ===== *)

Lemma choose_top_m_by_metric_complete_if_room :
  forall k metric jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    ~ In j (choose_top_m_by_metric k metric jobs m sched t candidates) ->
    length (choose_top_m_by_metric k metric jobs m sched t candidates) = k.
Proof.
  induction k as [|k' IH]; intros metric jobs m sched t candidates j Hin Helig Hnotin.
  - reflexivity.
  - destruct (choose_min_metric metric jobs m sched t candidates) as [best|] eqn:Hbest.
    + (* Rewrite Hnotin using the expansion lemma to expose the cons structure *)
      rewrite (choose_top_m_by_metric_Sn_some k' metric jobs m sched t candidates best Hbest)
        in Hnotin.
      rewrite (choose_top_m_by_metric_Sn_some k' metric jobs m sched t candidates best Hbest).
      destruct (Nat.eq_dec j best) as [Heq | Hneq].
      * (* j = best: j is the head, contradicts Hnotin *)
        subst best.
        exfalso. exact (Hnotin (in_eq j _)).
      * (* j ≠ best: apply IH on the tail *)
        simpl. f_equal.
        apply IH with (j := j).
        -- exact (@in_in_remove _ Nat.eq_dec candidates j best Hneq Hin).
        -- exact Helig.
        -- intros Hj. exact (Hnotin (in_cons best j _ Hj)).
    + (* choose_min_metric = None but j is eligible: contradiction *)
      exfalso.
      assert (Hexists : exists j', In j' candidates /\ eligible jobs m sched j' t)
        by (exists j; split; assumption).
      pose proof (choose_min_metric_some_if_exists metric jobs m sched t candidates Hexists)
        as [j' Hj'].
      rewrite Hj' in Hbest. discriminate.
Qed.

(* ===== Instance construction ===== *)

(** Build a GenericTopMSchedulingAlgorithm from a jobs-dependent metric.
    The algorithm picks the top m jobs by minimum metric value. *)
Definition make_metric_top_m_algorithm
    (metric_of_jobs : (JobId -> Job) -> JobId -> Z)
    : GenericTopMSchedulingAlgorithm :=
  mkGenericTopMSchedulingAlgorithm
    (* choose_top_m *)
    (fun jobs m sched t cands =>
       choose_top_m_by_metric m (metric_of_jobs jobs) jobs m sched t cands)
    (* choose_top_m_nodup *)
    (fun jobs m sched t cands =>
       choose_top_m_by_metric_nodup m (metric_of_jobs jobs) jobs m sched t cands)
    (* choose_top_m_in_candidates *)
    (fun jobs m sched t cands j H =>
       choose_top_m_by_metric_in_candidates
         m (metric_of_jobs jobs) jobs m sched t cands j H)
    (* choose_top_m_eligible *)
    (fun jobs m sched t cands j H =>
       choose_top_m_by_metric_eligible
         m (metric_of_jobs jobs) jobs m sched t cands j H)
    (* choose_top_m_length_le_m *)
    (fun jobs m sched t cands =>
       choose_top_m_by_metric_length_le
         m (metric_of_jobs jobs) jobs m sched t cands)
    (* choose_top_m_complete_if_room *)
    (fun jobs m sched t cands j Hin Helig Hnotin =>
       choose_top_m_by_metric_complete_if_room
         m (metric_of_jobs jobs) jobs m sched t cands j Hin Helig Hnotin).
