From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import DispatchInterface.
Import ListNotations.

(* Policy-independent lemmas derived from GenericDispatchSpec.
   All results hold for any concrete scheduler satisfying the interface.
   EDF-specific facts (choose_min_deadline, min-deadline corollaries) live
   in EDF.v under EDFSchedulerSpec. *)

(* ===== Coverage Predicates ===== *)
(* These predicates characterise how well the candidate list covers the eligible set. *)

(* candidates_sound: every candidate is eligible. *)
Definition candidates_sound (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, In j candidates -> eligible jobs m sched j t.

(* candidates_complete: every eligible job is in the candidate list. *)
Definition candidates_complete (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, eligible jobs m sched j t -> In j candidates.

Section DispatchLemmasSection.

  Variable spec        : GenericDispatchSpec.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* ===== A. Soundness Lemmas ===== *)
  (* Properties that the chosen job satisfies. *)

  (* A1: the chosen job is eligible. *)
  Lemma choose_some_implies_eligible :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        eligible jobs m sched j t.
  Proof.
    intros j Hchoose.
    exact (spec.(dispatch_eligible) jobs m sched t candidates j Hchoose).
  Qed.

  (* A2: the chosen job has been released by time t. *)
  Lemma choose_some_implies_released :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        released jobs j t.
  Proof.
    intros j Hchoose.
    apply choose_some_implies_eligible in Hchoose.
    exact (proj1 Hchoose).
  Qed.

  (* A3: the chosen job has not completed by time t. *)
  Lemma choose_some_implies_not_completed :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        ~completed jobs m sched j t.
  Proof.
    intros j Hchoose.
    apply choose_some_implies_eligible in Hchoose.
    exact (proj2 Hchoose).
  Qed.

  (* ===== B. Completeness Lemmas ===== *)
  (* Characterisation of when choose returns Some vs None. *)

  (* B1: if an eligible candidate exists, the dispatcher returns Some. *)
  Lemma eligible_exists_implies_choose_some :
      (exists j, In j candidates /\ eligible jobs m sched j t) ->
      exists j', spec.(dispatch) jobs m sched t candidates = Some j'.
  Proof.
    intro Hex.
    exact (spec.(dispatch_some_if_eligible_candidate) jobs m sched t candidates Hex).
  Qed.

  (* B2: if the dispatcher returns None, no candidate is eligible. *)
  Lemma choose_none_implies_no_eligible :
      spec.(dispatch) jobs m sched t candidates = None ->
      forall j, In j candidates -> ~eligible jobs m sched j t.
  Proof.
    intros Hnone j Hin Helig.
    assert (Hex : exists j', spec.(dispatch) jobs m sched t candidates = Some j').
    { apply eligible_exists_implies_choose_some. exists j. split; assumption. }
    destruct Hex as [j' Hj'].
    rewrite Hj' in Hnone. discriminate.
  Qed.

  (* B3: the dispatcher returns None iff no candidate is eligible. *)
  Lemma choose_none_iff_no_eligible :
      spec.(dispatch) jobs m sched t candidates = None <->
      forall j, In j candidates -> ~eligible jobs m sched j t.
  Proof.
    split.
    - apply choose_none_implies_no_eligible.
    - apply spec.(dispatch_none_if_no_eligible_candidate).
  Qed.

  (* B4: with an empty candidate list, the dispatcher always returns None. *)
  Lemma choose_none_if_candidates_empty :
      spec.(dispatch) jobs m sched t [] = None.
  Proof.
    apply spec.(dispatch_none_if_no_eligible_candidate).
    intros j Hin.
    inversion Hin.
  Qed.

  (* ===== D. Derived Consequences ===== *)

  (* D1: the chosen job's release time is at most t. *)
  Lemma choose_some_not_running_before_release :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        job_release (jobs j) <= t.
  Proof.
    intros j Hchoose.
    apply choose_some_implies_released in Hchoose.
    unfold released in Hchoose.
    exact Hchoose.
  Qed.

  (* D2: the chosen job has positive cost, assuming valid_jobs. *)
  Lemma choose_some_cost_positive_if_valid_jobs :
      valid_jobs jobs ->
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        0 < job_cost (jobs j).
  Proof.
    intros Hvj j _Hchoose.
    exact (Hvj j).
  Qed.

  (* ===== E. Membership Lemmas ===== *)
  (* Consequences of the dispatch_in_candidates spec field. *)

  (* E1: the chosen job is always in the candidate list. *)
  Lemma choose_some_implies_in_candidates :
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        In j candidates.
  Proof.
    intros j H.
    exact (spec.(dispatch_in_candidates) jobs m sched t candidates j H).
  Qed.

  (* E2: if an eligible candidate exists, choose does not return None. *)
  Lemma exists_eligible_candidate_implies_not_none :
      (exists j, In j candidates /\ eligible jobs m sched j t) ->
      spec.(dispatch) jobs m sched t candidates <> None.
  Proof.
    intros Hex Hnone.
    destruct (eligible_exists_implies_choose_some Hex) as [j' Hj'].
    rewrite Hnone in Hj'. discriminate.
  Qed.

  (* ===== F. Coverage Lemmas ===== *)
  (* Lemmas parametrised over the coverage predicates defined above. *)

  (* F3: under sound candidates, the chosen job is in the list and eligible. *)
  Lemma choose_some_under_sound_candidates :
      candidates_sound jobs m sched t candidates ->
      forall j,
        spec.(dispatch) jobs m sched t candidates = Some j ->
        In j candidates /\ eligible jobs m sched j t.
  Proof.
    intros Hsound j Hchoose.
    split.
    - exact (choose_some_implies_in_candidates j Hchoose).
    - exact (choose_some_implies_eligible j Hchoose).
  Qed.

  (* F4: under complete candidates, any eligible job implies choose returns Some. *)
  Lemma choose_some_if_any_eligible_under_complete_candidates :
      candidates_complete jobs m sched t candidates ->
      (exists j, eligible jobs m sched j t) ->
      exists j', spec.(dispatch) jobs m sched t candidates = Some j'.
  Proof.
    intros Hcomplete [j Helig].
    apply eligible_exists_implies_choose_some.
    exists j. split.
    - apply Hcomplete. exact Helig.
    - exact Helig.
  Qed.

End DispatchLemmasSection.
