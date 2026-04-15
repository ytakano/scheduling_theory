From Stdlib Require Import Arith Arith.PeanoNat Lia List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Common.WorkloadAggregation.
From RocqSched Require Import Analysis.Multicore.ProcessorSupply.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.

Import ListNotations.

(* Aggregate the service received by a list of jobs over an interval. *)
Fixpoint total_service_between_list
    (m : nat) (sched : Schedule) (l : list JobId) (t1 t2 : Time) : nat :=
  match l with
  | [] => 0
  | j :: l' =>
      service_between m sched j t1 t2 +
      total_service_between_list m sched l' t1 t2
  end.

(* Count how many CPUs are running jobs from the list at time t. *)
Fixpoint covered_cpu_count
    (m : nat) (sched : Schedule) (l : list JobId) (t : Time) : nat :=
  match m with
  | 0 => 0
  | S m' =>
      (match sched t m' with
       | Some j =>
           if in_dec Nat.eq_dec j l then 1 else 0
       | None => 0
       end) + covered_cpu_count m' sched l t
  end.

Definition covers_running_jobs
    (m : nat) (sched : Schedule) (l : list JobId) (t : Time) : Prop :=
  forall c j, c < m -> sched t c = Some j -> In j l.

Lemma covered_cpu_count_nil :
  forall m sched t,
    covered_cpu_count m sched [] t = 0.
Proof.
  induction m as [|m IH]; intros sched t; simpl; [reflexivity|].
  rewrite IH.
  destruct (sched t m); reflexivity.
Qed.

Lemma total_service_between_list_refl :
  forall m sched l t,
    total_service_between_list m sched l t t = 0.
Proof.
  intros m sched l t.
  induction l as [|j l IH]; simpl.
  - reflexivity.
  - rewrite service_between_refl, IH. lia.
Qed.

Lemma total_service_between_list_split :
  forall m sched l t1 t2 t3,
    t1 <= t2 ->
    t2 <= t3 ->
    total_service_between_list m sched l t1 t3 =
    total_service_between_list m sched l t1 t2 +
    total_service_between_list m sched l t2 t3.
Proof.
  intros m sched l t1 t2 t3 H12 H23.
  induction l as [|j l IH]; simpl.
  - reflexivity.
  - rewrite (service_between_split m sched j t1 t2 t3) by lia.
    rewrite IH by lia.
    lia.
Qed.

Lemma total_service_between_list_app :
  forall m sched l1 l2 t1 t2,
    total_service_between_list m sched (l1 ++ l2) t1 t2 =
    total_service_between_list m sched l1 t1 t2 +
    total_service_between_list m sched l2 t1 t2.
Proof.
  intros m sched l1 l2 t1 t2.
  induction l1 as [|j l1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma covered_cpu_count_eq_total_cpu_service_at :
  forall m sched l t,
    covers_running_jobs m sched l t ->
    covered_cpu_count m sched l t =
    total_cpu_service_at m sched t.
Proof.
  induction m as [|m IH]; intros sched l t Hcover.
  - reflexivity.
  - simpl.
    destruct (sched t m) as [j|] eqn:Hsched.
    + assert (Hin : In j l).
      { apply (Hcover m j); [lia | exact Hsched]. }
      destruct (in_dec Nat.eq_dec j l); [|contradiction].
      rewrite IH.
      * lia.
      * intros c j' Hlt Hrun.
        apply (Hcover c j').
        -- lia.
        -- exact Hrun.
    + rewrite IH.
      * lia.
      * intros c j Hlt Hrun.
        apply (Hcover c j).
        -- lia.
        -- exact Hrun.
Qed.

Lemma in_cons_neq_iff :
  forall (x y : JobId) (l : list JobId),
    x <> y ->
    (In x (y :: l) <-> In x l).
Proof.
  intros x y l Hneq.
  split.
  - intros [Heq | Hin].
    + exfalso. apply Hneq. symmetry. exact Heq.
    + exact Hin.
  - intros Hin.
    right.
    exact Hin.
Qed.

Lemma covered_cpu_count_cons :
  forall m sched j l t,
    no_duplication m sched ->
    ~ In j l ->
    covered_cpu_count m sched (j :: l) t =
    cpu_count m sched j t + covered_cpu_count m sched l t.
Proof.
  induction m as [|m IH]; intros sched j l t Hnd Hnotin.
  - reflexivity.
  - assert (Hnd_tail : no_duplication m sched).
    { intros j0 t0 c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
      apply (Hnd j0 t0 c1 c2).
      - lia.
      - lia.
      - exact Hrun1.
      - exact Hrun2.
    }
    destruct (runs_on sched j t m) eqn:Hruns.
    + assert (Hrunj : sched t m = Some j).
      { apply runs_on_true_iff. exact Hruns. }
      assert (Hzero : cpu_count m sched j t = 0).
      { pose proof (no_duplication_cpu_count_le_1 (S m) sched j t Hnd) as Hle.
        simpl in Hle.
        rewrite Hruns in Hle.
        lia.
      }
      assert (Hcovered_cons :
        covered_cpu_count (S m) sched (j :: l) t =
        1 + covered_cpu_count m sched (j :: l) t).
      { simpl.
        rewrite Hrunj.
        destruct (Nat.eq_dec j j) as [_ | Hneqjj].
        - reflexivity.
        - contradiction.
      }
      assert (Hcovered_l :
        covered_cpu_count (S m) sched l t =
        covered_cpu_count m sched l t).
      { simpl.
        rewrite Hrunj.
        destruct (in_dec Nat.eq_dec j l) as [Hin_l | Hnotin_l].
        - exfalso. apply Hnotin. exact Hin_l.
        - reflexivity.
      }
      assert (Htail :
        covered_cpu_count m sched (j :: l) t =
        covered_cpu_count m sched l t).
      { rewrite (IH sched j l t Hnd_tail Hnotin).
        rewrite Hzero.
        lia.
      }
      rewrite Hcovered_cons, Hcovered_l.
      rewrite Htail.
      simpl.
      rewrite Hruns, Hzero.
      lia.
    + destruct (sched t m) as [j_run|] eqn:Hsched.
      * assert (Hneqj : j_run <> j).
        { intro Heq.
          apply (proj1 (runs_on_false_iff sched j t m) Hruns).
          subst j_run.
          exact Hsched.
        }
        destruct (in_dec Nat.eq_dec j_run (j :: l)) as [Hin_cons | Hnotin_cons].
        -- apply (proj1 (in_cons_neq_iff j_run j l Hneqj)) in Hin_cons.
          destruct (in_dec Nat.eq_dec j_run l) as [Hin_l | Hnotin_l].
          ++ assert (Hcovered_cons :
               covered_cpu_count (S m) sched (j :: l) t =
               1 + covered_cpu_count m sched (j :: l) t).
             { cbn [covered_cpu_count].
               rewrite Hsched.
               change
                 ((if in_dec Nat.eq_dec j_run (j :: l) then 1 else 0) +
                  covered_cpu_count m sched (j :: l) t =
                  1 + covered_cpu_count m sched (j :: l) t).
               destruct (in_dec Nat.eq_dec j_run (j :: l)) as [Hin_cons' | Hnotin_cons'].
               - reflexivity.
               - exfalso. apply Hnotin_cons'. right. exact Hin_l.
             }
             assert (Hcovered_l :
               covered_cpu_count (S m) sched l t =
               1 + covered_cpu_count m sched l t).
             { simpl.
               rewrite Hsched.
               destruct (in_dec Nat.eq_dec j_run l) as [Hin_l' | Hnotin_l'].
               - reflexivity.
               - contradiction.
             }
             rewrite Hcovered_cons, Hcovered_l.
             simpl.
             rewrite Hruns.
             rewrite (IH sched j l t Hnd_tail Hnotin).
             lia.
           ++ contradiction.
        -- destruct (in_dec Nat.eq_dec j_run l) as [Hin_l | Hnotin_l].
           ++ exfalso.
              apply Hnotin_cons.
              apply (proj2 (in_cons_neq_iff j_run j l Hneqj)).
              exact Hin_l.
           ++ assert (Hcovered_cons :
                covered_cpu_count (S m) sched (j :: l) t =
                covered_cpu_count m sched (j :: l) t).
              { cbn [covered_cpu_count].
                rewrite Hsched.
                change
                  ((if in_dec Nat.eq_dec j_run (j :: l) then 1 else 0) +
                   covered_cpu_count m sched (j :: l) t =
                   covered_cpu_count m sched (j :: l) t).
                destruct (in_dec Nat.eq_dec j_run (j :: l)) as [Hin_cons' | Hnotin_cons'].
                - contradiction.
                - reflexivity.
              }
              assert (Hcovered_l :
                covered_cpu_count (S m) sched l t =
                covered_cpu_count m sched l t).
              { simpl.
                rewrite Hsched.
                destruct (in_dec Nat.eq_dec j_run l) as [Hin_l' | Hnotin_l'].
                - contradiction.
                - reflexivity.
              }
              rewrite Hcovered_cons, Hcovered_l.
              simpl.
              rewrite Hruns.
              rewrite (IH sched j l t Hnd_tail Hnotin).
              lia.
      * simpl.
        rewrite Hsched.
        rewrite Hruns.
        rewrite (IH sched j l t Hnd_tail Hnotin).
        lia.
Qed.

Lemma total_service_between_list_single_slot_eq_covered_cpu_count :
  forall m sched l t,
    no_duplication m sched ->
    NoDup l ->
    total_service_between_list m sched l t (S t) =
    covered_cpu_count m sched l t.
Proof.
  intros m sched l t Hnd Hnodup.
  induction l as [|j l IH]; simpl.
  - rewrite covered_cpu_count_nil. reflexivity.
  - inversion Hnodup as [|j' l' Hnotin Hnodup']; subst j' l'.
    rewrite service_between_single_slot_eq_cpu_count.
    rewrite IH by assumption.
    rewrite covered_cpu_count_cons by assumption.
    lia.
Qed.

Lemma total_service_between_list_covers_total_cpu_supply :
  forall m sched l t1 t2,
    no_duplication m sched ->
    NoDup l ->
    t1 <= t2 ->
    (forall t, t1 <= t < t2 -> covers_running_jobs m sched l t) ->
    total_cpu_service_between m sched t1 t2 =
    total_service_between_list m sched l t1 t2.
Proof.
  intros m sched l t1 t2 Hnd Hnodup Hle12 Hcover.
  remember (t2 - t1) as len eqn:Hlen.
  revert t1 t2 Hle12 Hlen Hcover.
  induction len as [|len IH]; intros t1 t2 Hle12 Hlen Hcover.
  - assert (t2 = t1) by lia.
    subst t2.
    rewrite total_cpu_service_between_refl.
    rewrite total_service_between_list_refl.
    reflexivity.
  - assert (Ht1t2 : t1 < t2) by lia.
    rewrite (total_cpu_service_between_split m sched t1 (S t1) t2) by lia.
    rewrite (total_service_between_list_split m sched l t1 (S t1) t2) by lia.
    assert (Hslot :
      total_cpu_service_between m sched t1 (S t1) =
      total_service_between_list m sched l t1 (S t1)).
    { rewrite total_cpu_service_between_single_slot.
      rewrite total_service_between_list_single_slot_eq_covered_cpu_count by assumption.
      symmetry.
      apply covered_cpu_count_eq_total_cpu_service_at.
      apply Hcover.
      lia.
    }
    assert (Hrest :
      total_cpu_service_between m sched (S t1) t2 =
      total_service_between_list m sched l (S t1) t2).
    { apply IH.
      - lia.
      - lia.
      - intros t Hrange.
        apply Hcover.
        lia.
    }
    rewrite Hslot, Hrest.
    lia.
Qed.

Lemma total_service_between_list_lt_total_job_cost_if_one_job_misses :
  forall jobs m sched l1 l2 j t1 t2,
    t1 <= t2 ->
    service_between m sched j t1 t2 < job_cost (jobs j) ->
    total_service_between_list m sched l1 t1 t2 <= total_job_cost jobs l1 ->
    total_service_between_list m sched l2 t1 t2 <= total_job_cost jobs l2 ->
    total_service_between_list m sched (l1 ++ j :: l2) t1 t2 <
    total_job_cost jobs (l1 ++ j :: l2).
Proof.
  intros jobs m sched l1 l2 j t1 t2 _ Hmiss Hle1 Hle2.
  rewrite !total_service_between_list_app.
  simpl.
  rewrite !total_job_cost_app.
  simpl.
  lia.
Qed.
