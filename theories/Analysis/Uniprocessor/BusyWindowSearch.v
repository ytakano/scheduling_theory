From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.
From RocqSched Require Import Analysis.Uniprocessor.BusyIntervalLemmas.

(* A busy-window candidate is a maximal busy interval on the single CPU. *)
Definition busy_window_candidate
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  maximal_busy_interval_from sched t1 t2.

(* A finite-horizon search candidate only requires a busy prefix with a
   left boundary; it need not end in an idle slot. *)
Definition busy_prefix_candidate
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  busy_interval sched t1 t2 /\
  (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)).

(* A search witness covers the distinguished time point t. *)
Definition busy_window_witness
    (sched : Schedule) (t : Time) (t1 t2 : Time) : Prop :=
  busy_window_candidate sched t1 t2 /\
  t1 <= t /\ t <= t2.

(* A finite-horizon witness only requires a covering busy prefix. *)
Definition busy_prefix_witness
    (sched : Schedule) (t : Time) (t1 t2 : Time) : Prop :=
  busy_prefix_candidate sched t1 t2 /\
  t1 <= t /\ t <= t2.

Lemma busy_window_candidate_is_maximal_busy_interval :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    maximal_busy_interval_from sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  exact Hcand.
Qed.

Lemma maximal_busy_interval_is_busy_window_candidate :
  forall sched t1 t2,
    maximal_busy_interval_from sched t1 t2 ->
    busy_window_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hmax.
  exact Hmax.
Qed.

Lemma busy_window_candidate_is_busy_prefix_candidate :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    busy_prefix_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  destruct (maximal_busy_interval_from_decompose sched t1 t2 Hcand) as [Hbusy [Hleft _]].
  split; assumption.
Qed.

Lemma busy_prefix_candidate_decompose :
  forall sched t1 t2,
    busy_prefix_candidate sched t1 t2 ->
    busy_interval sched t1 t2 /\
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)).
Proof.
  intros sched t1 t2 Hcand.
  exact Hcand.
Qed.

Lemma busy_prefix_candidate_busy_interval :
  forall sched t1 t2,
    busy_prefix_candidate sched t1 t2 ->
    busy_interval sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  exact (proj1 (busy_prefix_candidate_decompose sched t1 t2 Hcand)).
Qed.

Lemma busy_prefix_candidate_left_boundary :
  forall sched t1 t2,
    busy_prefix_candidate sched t1 t2 ->
    t1 = 0 \/ ~ cpu_busy_at sched (pred t1).
Proof.
  intros sched t1 t2 Hcand.
  exact (proj2 (busy_prefix_candidate_decompose sched t1 t2 Hcand)).
Qed.

Lemma idle_slot_not_busy_prefix_candidate :
  forall sched t1 t2 t,
    t1 <= t < t2 ->
    ~ cpu_busy_at sched t ->
    ~ busy_prefix_candidate sched t1 t2.
Proof.
  intros sched t1 t2 t Ht Hidle Hcand.
  eapply idle_slot_not_busy_interval; eauto.
  exact (busy_prefix_candidate_busy_interval sched t1 t2 Hcand).
Qed.

Lemma idle_slot_not_busy_prefix_witness :
  forall sched d t1 t2 t,
    t1 <= t < t2 ->
    ~ cpu_busy_at sched t ->
    ~ busy_prefix_witness sched d t1 t2.
Proof.
  intros sched d t1 t2 t Ht Hidle [Hcand _].
  eapply idle_slot_not_busy_prefix_candidate; eauto.
Qed.

Lemma busy_window_candidate_decompose :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    busy_interval sched t1 t2 /\
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) /\
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 Hcand.
  apply maximal_busy_interval_from_decompose.
  exact Hcand.
Qed.

Lemma busy_window_candidate_busy_interval :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    busy_interval sched t1 t2.
Proof.
  intros sched t1 t2 Hcand.
  exact (proj1 (busy_window_candidate_decompose sched t1 t2 Hcand)).
Qed.

Lemma busy_window_candidate_left_boundary :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    t1 = 0 \/ ~ cpu_busy_at sched (pred t1).
Proof.
  intros sched t1 t2 Hcand.
  exact (proj1 (proj2 (busy_window_candidate_decompose sched t1 t2 Hcand))).
Qed.

Lemma busy_window_candidate_right_boundary :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    ~ cpu_busy_at sched t2.
Proof.
  intros sched t1 t2 Hcand.
  exact (proj2 (proj2 (busy_window_candidate_decompose sched t1 t2 Hcand))).
Qed.

Lemma busy_interval_with_boundaries_is_busy_window_candidate :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) ->
    ~ cpu_busy_at sched t2 ->
    busy_window_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hbusy Hleft Hright.
  unfold busy_window_candidate, maximal_busy_interval_from.
  split; [exact Hbusy |].
  split; assumption.
Qed.

Lemma busy_interval_with_left_boundary_is_busy_prefix_candidate :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) ->
    busy_prefix_candidate sched t1 t2.
Proof.
  intros sched t1 t2 Hbusy Hleft.
  split; assumption.
Qed.

Lemma busy_window_candidate_covers_time :
  forall sched t t1 t2,
    busy_window_witness sched t t1 t2 ->
    t1 <= t /\ t <= t2.
Proof.
  intros sched t t1 t2 [_ Hcover].
  exact Hcover.
Qed.

Lemma busy_prefix_candidate_covers_time :
  forall sched t t1 t2,
    busy_prefix_witness sched t t1 t2 ->
    t1 <= t /\ t <= t2.
Proof.
  intros sched t t1 t2 [_ Hcover].
  exact Hcover.
Qed.

Lemma busy_window_candidate_covers_deadline :
  forall (jobs : JobId -> Job) sched j t1 t2,
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_abs_deadline (jobs j) /\
    job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs sched j t1 t2 Hwit.
  exact (busy_window_candidate_covers_time sched (job_abs_deadline (jobs j)) t1 t2 Hwit).
Qed.

Lemma busy_prefix_candidate_covers_deadline :
  forall (jobs : JobId -> Job) sched j t1 t2,
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2 ->
    t1 <= job_abs_deadline (jobs j) /\
    job_abs_deadline (jobs j) <= t2.
Proof.
  intros jobs sched j t1 t2 Hwit.
  exact (busy_prefix_candidate_covers_time sched (job_abs_deadline (jobs j)) t1 t2 Hwit).
Qed.

Lemma busy_window_witness_from_candidate :
  forall sched t t1 t2,
    busy_window_candidate sched t1 t2 ->
    t1 <= t ->
    t <= t2 ->
    busy_window_witness sched t t1 t2.
Proof.
  intros sched t t1 t2 Hcand Hleft Hright.
  split; [exact Hcand | lia].
Qed.

Lemma busy_prefix_witness_from_candidate :
  forall sched t t1 t2,
    busy_prefix_candidate sched t1 t2 ->
    t1 <= t ->
    t <= t2 ->
    busy_prefix_witness sched t t1 t2.
Proof.
  intros sched t t1 t2 Hcand Hleft Hright.
  split; [exact Hcand | lia].
Qed.

Lemma busy_window_witness_implies_busy_prefix_witness :
  forall sched t t1 t2,
    busy_window_witness sched t t1 t2 ->
    busy_prefix_witness sched t t1 t2.
Proof.
  intros sched t t1 t2 [Hcand Hcover].
  split.
  - exact (busy_window_candidate_is_busy_prefix_candidate sched t1 t2 Hcand).
  - exact Hcover.
Qed.

Lemma busy_window_witness_monotone :
  forall sched t t1 t2 t1' t2',
    busy_window_witness sched t t1 t2 ->
    t1' <= t1 ->
    t2 <= t2' ->
    busy_window_candidate sched t1 t2 ->
    t1' <= t /\ t <= t2'.
Proof.
  intros sched t t1 t2 t1' t2' Hwit Hleft Hright _.
  destruct Hwit as [_ [Hge Hle]].
  lia.
Qed.

Lemma deadline_miss_inside_busy_window_candidate :
  forall (jobs : JobId -> Job) sched j t1 t2,
    missed_deadline jobs 1 sched j ->
    busy_window_candidate sched t1 t2 ->
    t1 <= job_abs_deadline (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    busy_window_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j t1 t2 _ Hcand Hleft Hright.
  apply busy_window_witness_from_candidate; assumption.
Qed.

Lemma deadline_miss_inside_busy_prefix_candidate :
  forall (jobs : JobId -> Job) sched j t1 t2,
    missed_deadline jobs 1 sched j ->
    busy_prefix_candidate sched t1 t2 ->
    t1 <= job_abs_deadline (jobs j) ->
    job_abs_deadline (jobs j) <= t2 ->
    busy_prefix_witness sched (job_abs_deadline (jobs j)) t1 t2.
Proof.
  intros jobs sched j t1 t2 _ Hcand Hleft Hright.
  apply busy_prefix_witness_from_candidate; assumption.
Qed.

Lemma busy_window_candidate_cpu_supply_eq_length :
  forall sched t1 t2,
    busy_window_candidate sched t1 t2 ->
    cpu_service_between sched t1 t2 = t2 - t1.
Proof.
  intros sched t1 t2 Hcand.
  apply cpu_service_between_busy_interval_eq_length.
  apply busy_window_candidate_busy_interval.
  exact Hcand.
Qed.

Lemma busy_prefix_candidate_cpu_supply_eq_length :
  forall sched t1 t2,
    busy_prefix_candidate sched t1 t2 ->
    cpu_service_between sched t1 t2 = t2 - t1.
Proof.
  intros sched t1 t2 Hcand.
  apply cpu_service_between_busy_interval_eq_length.
  apply busy_prefix_candidate_busy_interval.
  exact Hcand.
Qed.

Fixpoint busy_prefix_start (sched : Schedule) (t : Time) : Time :=
  match t with
  | 0 => 0
  | S t' =>
      match sched t' 0 with
      | Some _ => busy_prefix_start sched t'
      | None => S t'
      end
  end.

Lemma busy_prefix_start_le :
  forall sched t,
    busy_prefix_start sched t <= t.
Proof.
  intros sched t.
  induction t as [|t' IH].
  - reflexivity.
  - simpl.
    destruct (sched t' 0); lia.
Qed.

Lemma busy_prefix_start_left_boundary :
  forall sched t,
    busy_prefix_start sched t = 0 \/
    ~ cpu_busy_at sched (pred (busy_prefix_start sched t)).
Proof.
  intros sched t.
  induction t as [|t' IH].
  - left. reflexivity.
  - simpl.
    destruct (sched t' 0) as [j|] eqn:Hsched.
    + exact IH.
    + right.
      unfold cpu_busy_at.
      rewrite Nat.pred_succ.
      intros [j' Hbusy].
      rewrite Hsched in Hbusy.
      discriminate.
Qed.

Lemma busy_prefix_start_busy_from :
  forall sched t,
    cpu_busy_at sched t ->
    forall x,
      busy_prefix_start sched t <= x <= t ->
      cpu_busy_at sched x.
Proof.
  intros sched t Hbusy.
  induction t as [|t' IH]; intros x Hrange.
  - assert (x = 0) by lia.
    subst x.
    exact Hbusy.
  - simpl in *.
    destruct (sched t' 0) as [j'|] eqn:Hsched.
    + destruct (Nat.eq_dec x (S t')) as [-> | Hneq].
      * exact Hbusy.
      * apply IH.
        -- exists j'. exact Hsched.
        -- lia.
    + assert (Hstart : busy_prefix_start sched (S t') = S t').
      { simpl. rewrite Hsched. reflexivity. }
      assert (S t' <= x) by lia.
      assert (x = S t') by lia.
      subst x.
      exact Hbusy.
Qed.

Lemma busy_prefix_start_is_busy_prefix_candidate :
  forall sched t,
    cpu_busy_at sched t ->
    busy_prefix_candidate sched (busy_prefix_start sched t) (S t).
Proof.
  intros sched t Hbusy.
  apply busy_interval_with_left_boundary_is_busy_prefix_candidate.
  - split.
    + pose proof (busy_prefix_start_le sched t) as Hstart.
      lia.
    + intros x Hx.
      apply busy_prefix_start_busy_from with (t := t); try assumption.
      lia.
  - apply busy_prefix_start_left_boundary.
Qed.

Lemma busy_prefix_witness_exists_from_busy_time :
  forall sched t,
    cpu_busy_at sched t ->
    exists t1 t2,
      busy_prefix_witness sched t t1 t2.
Proof.
  intros sched t Hbusy.
  exists (busy_prefix_start sched t), (S t).
  apply busy_prefix_witness_from_candidate.
  - apply busy_prefix_start_is_busy_prefix_candidate.
    exact Hbusy.
  - apply busy_prefix_start_le.
  - lia.
Qed.

Fixpoint first_idle_from (sched : Schedule) (t fuel : Time) : Time :=
  match fuel with
  | 0 => t
  | S fuel' =>
      match sched t 0 with
      | Some _ => first_idle_from sched (S t) fuel'
      | None => t
      end
  end.

Lemma first_idle_from_bounds :
  forall sched t fuel,
    t <= first_idle_from sched t fuel <= t + fuel.
Proof.
  intros sched t fuel.
  revert t.
  induction fuel as [|fuel' IH]; intros t.
  - simpl. lia.
  - simpl.
    destruct (sched t 0) as [j|] eqn:Hsched.
    + specialize (IH (S t)).
      lia.
    + lia.
Qed.

Lemma first_idle_from_idle :
  forall sched t fuel r,
    t + fuel = r ->
    ~ cpu_busy_at sched r ->
    ~ cpu_busy_at sched (first_idle_from sched t fuel).
Proof.
  intros sched t fuel.
  revert t.
  induction fuel as [|fuel' IH]; intros t r Heq Hidle.
  - simpl in *.
    subst r.
    replace (t + 0) with t in Hidle by lia.
    exact Hidle.
  - simpl.
    destruct (sched t 0) as [j|] eqn:Hsched.
    + apply IH with (r := r).
      * lia.
      * exact Hidle.
    + unfold cpu_busy_at.
      intros [j' Hbusy].
      rewrite Hsched in Hbusy.
      discriminate.
Qed.

Lemma first_idle_from_busy_interval :
  forall sched t fuel x,
    x < first_idle_from sched t fuel ->
    t <= x ->
    cpu_busy_at sched x.
Proof.
  intros sched t fuel.
  revert t.
  induction fuel as [|fuel' IH]; intros t x Hlt Htx.
  - simpl in Hlt. lia.
  - simpl in Hlt.
    destruct (sched t 0) as [j|] eqn:Hsched.
    + destruct (Nat.eq_dec x t) as [-> | Hneq].
      * exists j. exact Hsched.
      * apply IH with (t := S t); lia.
    + lia.
Qed.

Lemma first_idle_from_is_busy_window_candidate :
  forall sched t r,
    cpu_busy_at sched t ->
    t <= r ->
    ~ cpu_busy_at sched r ->
    busy_window_candidate sched (busy_prefix_start sched t)
      (first_idle_from sched (busy_prefix_start sched t)
         (r - busy_prefix_start sched t)).
Proof.
  intros sched t r Hbusy Htr Hidle.
  apply busy_interval_with_boundaries_is_busy_window_candidate.
  - split.
    + pose proof (busy_prefix_start_le sched t) as Hstart.
      assert (
        ~ cpu_busy_at sched
            (first_idle_from sched (busy_prefix_start sched t)
               (r - busy_prefix_start sched t))) as Ht2_idle.
      {
        eapply first_idle_from_idle with (r := r).
        - lia.
        - exact Hidle.
      }
      destruct (Nat.lt_ge_cases t
                  (first_idle_from sched (busy_prefix_start sched t)
                     (r - busy_prefix_start sched t))) as [Hlt | Hge].
      * lia.
      * exfalso.
        pose proof
          (busy_prefix_start_busy_from sched t Hbusy
             (first_idle_from sched (busy_prefix_start sched t)
                (r - busy_prefix_start sched t))) as Hbusy_t2.
        apply Ht2_idle.
        apply Hbusy_t2.
        pose proof (first_idle_from_bounds sched (busy_prefix_start sched t)
                      (r - busy_prefix_start sched t)) as [Hlo _].
        lia.
    + intros x Hx.
      eapply first_idle_from_busy_interval.
      * exact (proj2 Hx).
      * exact (proj1 Hx).
  - apply busy_prefix_start_left_boundary.
  - eapply first_idle_from_idle with (r := r).
    + pose proof (busy_prefix_start_le sched t) as Hstart.
      lia.
    + exact Hidle.
Qed.

Lemma busy_window_witness_exists_with_right_idle :
  forall sched t r,
    cpu_busy_at sched t ->
    t <= r ->
    ~ cpu_busy_at sched r ->
    exists t1 t2,
      busy_window_witness sched t t1 t2.
Proof.
  intros sched t r Hbusy Htr Hidle.
  exists (busy_prefix_start sched t).
  exists (first_idle_from sched (busy_prefix_start sched t)
            (r - busy_prefix_start sched t)).
  apply busy_window_witness_from_candidate.
  - eapply first_idle_from_is_busy_window_candidate; eauto.
  - apply busy_prefix_start_le.
  - pose proof (busy_prefix_start_le sched t) as Hstart.
    assert (Ht2_idle :
      ~ cpu_busy_at sched
          (first_idle_from sched (busy_prefix_start sched t)
             (r - busy_prefix_start sched t))).
    {
      eapply first_idle_from_idle with (r := r).
      - lia.
      - exact Hidle.
    }
    destruct (Nat.lt_ge_cases t
                (first_idle_from sched (busy_prefix_start sched t)
                   (r - busy_prefix_start sched t))) as [Hlt | Hge].
    + lia.
    + exfalso.
      pose proof (busy_prefix_start_busy_from sched t Hbusy
                    (first_idle_from sched (busy_prefix_start sched t)
                       (r - busy_prefix_start sched t))) as Hbusy_end.
      apply Ht2_idle.
      apply Hbusy_end.
      pose proof (first_idle_from_bounds sched (busy_prefix_start sched t)
                    (r - busy_prefix_start sched t)) as [Hlo _].
      lia.
Qed.
