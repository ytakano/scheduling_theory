From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import SchedulerValidity.
Require Import DispatcherRefinement.
Import ListNotations.

(* eligibleb and eligibleb_iff are defined in ScheduleModel and available via
   Require Import ScheduleModel above. *)

(* Select the job with the minimum absolute deadline from a list.
   Returns None iff the list is empty.
   Tie-breaking: the earlier element in the list wins (<=? is not strict). *)
Fixpoint min_dl_job (jobs : JobId -> Job) (l : list JobId) : option JobId :=
  match l with
  | []       => None
  | j :: rest =>
    match min_dl_job jobs rest with
    | None    => Some j
    | Some j' => if job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')
                 then Some j
                 else Some j'
    end
  end.

(* EDF dispatch function:
   From candidates, filter to those that are eligible, then select
   the one with the earliest (minimum) absolute deadline. *)
Definition choose_edf (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                       (t : Time) (candidates : list JobId) : option JobId :=
  min_dl_job jobs (filter (fun j => eligibleb jobs m sched j t) candidates).

(* ===== Phase 2: min_dl_job Structural Properties ===== *)

Lemma min_dl_job_none_iff : forall jobs l,
    min_dl_job jobs l = None <-> l = [].
Proof.
  intros jobs l. induction l as [| j rest IH]; simpl.
  - tauto.
  - split; [| discriminate].
    intro Hsome.
    destruct (min_dl_job jobs rest) as [j'|].
    + destruct (job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')); discriminate.
    + discriminate.
Qed.

Lemma min_dl_job_in : forall jobs l j,
    min_dl_job jobs l = Some j -> In j l.
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome.
    destruct (min_dl_job jobs rest) as [j'|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs j')) eqn:Ecmp.
      * injection Hsome as Heq. subst. left. reflexivity.
      * injection Hsome as Heq. subst. right. apply IH. reflexivity.
    + injection Hsome as Heq. subst. left. reflexivity.
Qed.

Lemma min_dl_job_min : forall jobs l j,
    min_dl_job jobs l = Some j ->
    forall j', In j' l ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs l. induction l as [| j0 rest IH]; simpl.
  - discriminate.
  - intros j Hsome j' Hin.
    destruct (min_dl_job jobs rest) as [jmin|] eqn:Erest.
    + destruct (job_abs_deadline (jobs j0) <=? job_abs_deadline (jobs jmin)) eqn:Ecmp.
      * (* chosen = j0 *)
        injection Hsome as Heq. subst j.
        apply Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- pose proof (IH jmin eq_refl j' Hin'). lia.
      * (* chosen = jmin; after subst jmin, j is the result *)
        injection Hsome as Heq. subst jmin.
        apply Bool.not_true_iff_false in Ecmp.
        rewrite Nat.leb_le in Ecmp.
        destruct Hin as [-> | Hin'].
        -- lia.
        -- apply IH. reflexivity. exact Hin'.
    + (* None branch: min_dl_job rest = None, so rest = [], j = j0 *)
      injection Hsome as Heq. subst j.
      destruct Hin as [-> | Hin'].
      * lia.
      * apply min_dl_job_none_iff in Erest. subst rest. contradiction.
Qed.

(* ===== Phase 2b: Additional min_dl_job / filter lemmas ===== *)

(* If no candidate is eligible, choose_edf returns None. *)
Lemma choose_edf_none_if_no_eligible : forall jobs m sched t candidates,
    (forall j, In j candidates -> ~eligible jobs m sched j t) ->
    choose_edf jobs m sched t candidates = None.
Proof.
  intros jobs m sched t candidates Hnone.
  unfold choose_edf.
  apply min_dl_job_none_iff.
  induction candidates as [| j0 rest IH].
  - reflexivity.
  - simpl. destruct (eligibleb jobs m sched j0 t) eqn:Erb.
    + exfalso. apply (Hnone j0 (or_introl eq_refl)).
      apply eligibleb_iff. exact Erb.
    + apply IH. intros j Hin. apply Hnone. right. exact Hin.
Qed.

(* ===== Phase 3: EDF Dispatch Correctness ===== *)

(* Theorem 1: The chosen job is eligible. *)
Theorem choose_edf_eligible : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates j Hchoose.
  unfold choose_edf in Hchoose.
  apply min_dl_job_in in Hchoose.
  apply filter_In in Hchoose.
  destruct Hchoose as [_ Hrb].
  apply eligibleb_iff. exact Hrb.
Qed.

(* Theorem 2: The chosen job has the minimum deadline among all eligible candidates. *)
Theorem choose_edf_min_deadline : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    eligible jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Hchoose j' Hin Helig.
  unfold choose_edf in Hchoose.
  apply (min_dl_job_min jobs _ j Hchoose).
  apply filter_In. split.
  - exact Hin.
  - apply eligibleb_iff. exact Helig.
Qed.

(* Theorem 3: A job is always chosen when an eligible candidate exists. *)
Theorem choose_edf_some_if_exists : forall jobs m sched t candidates,
    (exists j, In j candidates /\ eligible jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates [j [Hin Helig]].
  unfold choose_edf.
  assert (Hne : filter (fun j => eligibleb jobs m sched j t) candidates <> []).
  { intro Hempty.
    assert (Hin' : In j (filter (fun j => eligibleb jobs m sched j t) candidates)).
    { apply filter_In. split. exact Hin. apply eligibleb_iff. exact Helig. }
    rewrite Hempty in Hin'. contradiction. }
  destruct (min_dl_job jobs (filter (fun j => eligibleb jobs m sched j t) candidates))
      as [j'|] eqn:Hmin.
  - exists j'. reflexivity.
  - apply min_dl_job_none_iff in Hmin. contradiction.
Qed.

(* ===== Phase 4: Explicit Precondition Lemmas (NoDup + eligible-set coverage) ===== *)

(* B1: If candidates exactly represents the eligible set and an eligible job exists,
   choose_edf always returns Some. *)
Lemma choose_edf_complete : forall jobs m sched t candidates,
    (forall j, eligible jobs m sched j t <-> In j candidates) ->
    (exists j, eligible jobs m sched j t) ->
    exists j', choose_edf jobs m sched t candidates = Some j'.
Proof.
  intros jobs m sched t candidates Href [j Helig].
  apply choose_edf_some_if_exists.
  exists j. split.
  - apply Href. exact Helig.
  - exact Helig.
Qed.

(* B2: If candidates exactly represents the eligible set, the chosen job has
   minimum deadline in the entire eligible set. *)
Lemma choose_edf_optimal : forall jobs m sched t candidates j,
    (forall j', eligible jobs m sched j' t <-> In j' candidates) ->
    choose_edf jobs m sched t candidates = Some j ->
    forall j', eligible jobs m sched j' t ->
    job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
Proof.
  intros jobs m sched t candidates j Href Hchoose j' Helig.
  apply (choose_edf_min_deadline jobs m sched t candidates j Hchoose).
  - apply Href. exact Helig.
  - exact Helig.
Qed.

(* ===== Phase 5: Uniqueness / Determinism ===== *)

(* A2: If job j has strictly smaller deadline than every other eligible candidate,
   EDF is forced to return j. *)
Lemma choose_edf_unique_min : forall jobs m sched t candidates j,
    In j candidates ->
    eligible jobs m sched j t ->
    (forall j', In j' candidates -> eligible jobs m sched j' t ->
                j' <> j ->
                job_abs_deadline (jobs j) < job_abs_deadline (jobs j')) ->
    choose_edf jobs m sched t candidates = Some j.
Proof.
  intros jobs m sched t candidates j Hin Helig Hstrict.
  destruct (choose_edf_some_if_exists jobs m sched t candidates) as [j' Hchoose].
  { exists j. split. exact Hin. exact Helig. }
  assert (Hj'_elig : eligible jobs m sched j' t).
  { apply (choose_edf_eligible jobs m sched t candidates). exact Hchoose. }
  assert (Hj'_in : In j' candidates).
  { unfold choose_edf in Hchoose.
    apply min_dl_job_in in Hchoose.
    apply filter_In in Hchoose. exact (proj1 Hchoose). }
  assert (Hle : job_abs_deadline (jobs j') <= job_abs_deadline (jobs j)).
  { apply (choose_edf_min_deadline jobs m sched t candidates j' Hchoose j Hin Helig). }
  destruct (Nat.eq_dec j' j) as [Heq | Hneq].
  - rewrite Heq in Hchoose. exact Hchoose.
  - exfalso.
    pose proof (Hstrict j' Hj'_in Hj'_elig Hneq) as Hlt.
    lia.
Qed.

(* ===== Phase 6: EDF satisfies GenericDispatchSpec and EDFSchedulerSpec ===== *)

(* The chosen job is always a member of the candidate list. *)
Lemma choose_edf_in_candidates : forall jobs m sched t candidates j,
    choose_edf jobs m sched t candidates = Some j -> In j candidates.
Proof.
  intros jobs m sched t candidates j Hchoose.
  unfold choose_edf in Hchoose.
  apply min_dl_job_in in Hchoose.
  apply filter_In in Hchoose.
  exact (proj1 Hchoose).
Qed.

(* EDF satisfies the generic (policy-independent) dispatch interface. *)
Definition edf_generic_spec : GenericDispatchSpec :=
  mkGenericDispatchSpec
    choose_edf
    choose_edf_eligible
    choose_edf_some_if_exists
    choose_edf_none_if_no_eligible
    choose_edf_in_candidates.

(* EDF-specific scheduler spec: extends GenericDispatchSpec with the
   minimum-deadline invariant.  This is the full EDF interface. *)
Record EDFSchedulerSpec : Type := mkEDFSchedulerSpec {
  (* Sub-record coercion: an EDFSchedulerSpec can be used where a
     GenericDispatchSpec is expected. *)
  edf_generic :> GenericDispatchSpec ;

  (* EDF policy invariant: the chosen job has the minimum absolute deadline
     among all eligible candidates. *)
  edf_choose_min_deadline :
    forall jobs m sched t candidates j,
      dispatch edf_generic jobs m sched t candidates = Some j ->
      forall j', In j' candidates ->
      eligible jobs m sched j' t ->
      job_abs_deadline (jobs j) <= job_abs_deadline (jobs j') ;
}.

(* EDF is a concrete instance of EDFSchedulerSpec. *)
Definition edf_scheduler_spec : EDFSchedulerSpec :=
  mkEDFSchedulerSpec
    edf_generic_spec
    choose_edf_min_deadline.

(* ===== Phase 7: EDF-specific lemmas (policy invariant consequences) ===== *)

Section EDFSchedulerLemmasSection.

  Variable spec        : EDFSchedulerSpec.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* A5: the chosen job has minimum absolute deadline among all eligible candidates. *)
  Lemma edf_choose_some_implies_min_deadline :
      forall j j',
        spec.(dispatch) jobs m sched t candidates = Some j ->
        In j' candidates ->
        eligible jobs m sched j' t ->
        job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Helig.
    exact (spec.(edf_choose_min_deadline) jobs m sched t candidates j Hchoose j' Hin Helig).
  Qed.

  (* C1: no eligible candidate has strictly smaller deadline than the chosen job. *)
  Lemma edf_choose_some_implies_no_earlier_deadline_candidate :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        ~exists j', In j' candidates /\ eligible jobs m sched j' t /\
                    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
  Proof.
    intros j Hchoose [j' [Hin [Helig Hlt]]].
    pose proof (edf_choose_some_implies_min_deadline j j' Hchoose Hin Helig) as Hle.
    lia.
  Qed.

  (* C2: if an eligible candidate has deadline <= chosen deadline, they are equal. *)
  Lemma edf_choose_some_tie_deadline :
      forall j j',
        spec.(dispatch) jobs m sched t candidates = Some j ->
        In j' candidates ->
        eligible jobs m sched j' t ->
        job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) ->
        job_abs_deadline (jobs j) = job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Helig Hle.
    pose proof (edf_choose_some_implies_min_deadline j j' Hchoose Hin Helig) as Hle2.
    lia.
  Qed.

End EDFSchedulerLemmasSection.

(* Lift edf_generic_spec into a Scheduler relation for the single-CPU case.
   candidates_of supplies the candidate list at each time step. *)
Definition edf_scheduler
    (candidates_of : (JobId -> Job) -> nat -> Schedule -> Time -> list JobId)
    : Scheduler :=
  single_cpu_dispatch_schedule edf_generic_spec candidates_of.

(* ===== Phase 8: Abstract EDF policy ===== *)

(* Auxiliary: if choose_edf returns None, all candidates are ineligible.
   (Converse of choose_edf_none_if_no_eligible.) *)
Lemma choose_edf_none_implies_no_eligible : forall jobs m sched t candidates,
    choose_edf jobs m sched t candidates = None ->
    forall j, In j candidates -> ~eligible jobs m sched j t.
Proof.
  intros jobs m sched t candidates Hnone j Hin Helig.
  unfold choose_edf in Hnone.
  apply min_dl_job_none_iff in Hnone.
  assert (Hin' : In j (filter (fun j0 => eligibleb jobs m sched j0 t) candidates)).
  { apply filter_In. split. exact Hin. apply eligibleb_iff. exact Helig. }
  rewrite Hnone in Hin'. exact Hin'.
Qed.

(* Abstract EDF policy: ties are permitted (any job with minimum deadline wins).
   - None: all candidates are ineligible.
   - Some j: j is in the list, eligible, and has minimum deadline among
     all eligible candidates. *)
Definition edf_policy : DispatchPolicy :=
  fun jobs m sched t candidates oj =>
    match oj with
    | None =>
        forall j, In j candidates -> ~eligible jobs m sched j t
    | Some j =>
        In j candidates /\
        eligible jobs m sched j t /\
        forall j',
          In j' candidates ->
          eligible jobs m sched j' t ->
          job_abs_deadline (jobs j) <= job_abs_deadline (jobs j')
    end.

Lemma edf_policy_sane : PolicySanity edf_policy.
Proof.
  constructor.
  - intros jobs m sched t candidates j Hpol.
    unfold edf_policy in Hpol.
    exact (proj1 Hpol).
  - intros jobs m sched t candidates j Hpol.
    unfold edf_policy in Hpol.
    exact (proj1 (proj2 Hpol)).
Qed.

Lemma choose_edf_refines_edf_policy :
  dispatcher_refines_policy edf_generic_spec edf_policy.
Proof.
  unfold dispatcher_refines_policy.
  intros jobs m sched t candidates.
  unfold edf_policy. simpl.
  destruct (choose_edf jobs m sched t candidates) as [j|] eqn:Hchoose.
  - split.
    + exact (choose_edf_in_candidates jobs m sched t candidates j Hchoose).
    + split.
      * exact (choose_edf_eligible jobs m sched t candidates j Hchoose).
      * intros j' Hin Helig.
        exact (choose_edf_min_deadline jobs m sched t candidates j Hchoose j' Hin Helig).
  - intros j Hin Helig.
    exact (choose_edf_none_implies_no_eligible jobs m sched t candidates Hchoose j Hin Helig).
Qed.

(* ===== Phase 9: UniSchedulerBundle instance for EDF ===== *)

Require Import UniSchedulerInterface.
Require Import UniSchedulerLemmas.

(* Bundle that packages all EDF components into the standard UniSchedulerBundle
   interface.  Client supplies the candidate source; the rest is fixed to EDF. *)
Definition edf_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J :=
  mkUniSchedulerBundle J
    candidates_of
    cand_spec
    edf_generic_spec
    edf_policy
    edf_policy_sane
    choose_edf_refines_edf_policy.

(* Thin wrapper: concrete single-CPU EDF scheduler from a bundle. *)
Definition edf_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_scheduler_on (edf_bundle J candidates_of cand_spec).

(* Thin wrapper: abstract EDF policy scheduler from a bundle. *)
Definition edf_policy_scheduler_on
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
    : Scheduler :=
  uni_policy_scheduler_on (edf_bundle J candidates_of cand_spec).
