From Stdlib Require Import List Bool Arith Arith.PeanoNat Lia Classical.
Require Import Base.
Require Import Schedule.
Require Import UniSchedulerInterface.
Import ListNotations.

(* Policy-independent lemmas derived from UniSchedulerSpec.
   All results hold for any concrete scheduler satisfying the interface.
   No EDF-specific facts, no readyb, no min_dl_job. *)

(* ===== Coverage Predicates ===== *)
(* These predicates characterise how well the candidate list covers the ready set. *)

(* candidates_sound: every candidate is ready. *)
Definition candidates_sound (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, In j candidates -> ready jobs m sched j t.

(* candidates_complete: every ready job is in the candidate list. *)
Definition candidates_complete (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : Prop :=
  forall j, ready jobs m sched j t -> In j candidates.

Section UniSchedulerLemmasSection.

  Variable spec        : UniSchedulerSpec.
  Variable jobs        : JobId -> Job.
  Variable m           : nat.
  Variable sched       : Schedule.
  Variable t           : Time.
  Variable candidates  : list JobId.

  (* ===== A. Soundness Lemmas ===== *)
  (* Properties that the chosen job satisfies. *)

  (* A1: the chosen job is ready. *)
  Lemma choose_some_implies_ready :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        ready jobs m sched j t.
  Proof.
    intros j Hchoose.
    exact (spec.(choose_ready) jobs m sched t candidates j Hchoose).
  Qed.

  (* A2: the chosen job has been released by time t. *)
  Lemma choose_some_implies_released :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        released jobs j t.
  Proof.
    intros j Hchoose.
    apply choose_some_implies_ready in Hchoose.
    exact (proj1 (proj1 Hchoose)).
  Qed.

  (* A3: the chosen job has not completed by time t. *)
  Lemma choose_some_implies_not_completed :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        ~completed jobs m sched j t.
  Proof.
    intros j Hchoose.
    apply choose_some_implies_ready in Hchoose.
    exact (proj2 (proj1 Hchoose)).
  Qed.

  (* A5: the chosen job has minimum absolute deadline among all ready candidates. *)
  Lemma choose_some_implies_min_deadline :
      forall j j',
        spec.(choose) jobs m sched t candidates = Some j ->
        In j' candidates ->
        ready jobs m sched j' t ->
        job_abs_deadline (jobs j) <= job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Hready.
    exact (spec.(choose_min_deadline) jobs m sched t candidates j Hchoose j' Hin Hready).
  Qed.

  (* ===== B. Completeness Lemmas ===== *)
  (* Characterisation of when choose returns Some vs None. *)

  (* B1: if a ready candidate exists, the dispatcher returns Some. *)
  Lemma ready_exists_implies_choose_some :
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      exists j', spec.(choose) jobs m sched t candidates = Some j'.
  Proof.
    intro Hex.
    exact (spec.(choose_some_if_ready) jobs m sched t candidates Hex).
  Qed.

  (* B2: if the dispatcher returns None, no candidate is ready. *)
  Lemma choose_none_implies_no_ready :
      spec.(choose) jobs m sched t candidates = None ->
      forall j, In j candidates -> ~ready jobs m sched j t.
  Proof.
    intros Hnone j Hin Hready.
    assert (Hex : exists j', spec.(choose) jobs m sched t candidates = Some j').
    { apply ready_exists_implies_choose_some. exists j. split; assumption. }
    destruct Hex as [j' Hj'].
    rewrite Hj' in Hnone. discriminate.
  Qed.

  (* B3: the dispatcher returns None iff no candidate is ready. *)
  Lemma choose_none_iff_no_ready :
      spec.(choose) jobs m sched t candidates = None <->
      forall j, In j candidates -> ~ready jobs m sched j t.
  Proof.
    split.
    - apply choose_none_implies_no_ready.
    - apply spec.(choose_none_if_no_ready).
  Qed.

  (* B4: with an empty candidate list, the dispatcher always returns None. *)
  Lemma choose_none_if_candidates_empty :
      spec.(choose) jobs m sched t [] = None.
  Proof.
    apply spec.(choose_none_if_no_ready).
    intros j Hin.
    inversion Hin.
  Qed.

  (* ===== C. Min-deadline Corollaries ===== *)
  (* Valid because choose_min_deadline is part of UniSchedulerSpec. *)

  (* C1: no ready candidate has strictly smaller deadline than the chosen job. *)
  Lemma choose_some_implies_no_earlier_deadline_candidate :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        ~exists j', In j' candidates /\ ready jobs m sched j' t /\
                    job_abs_deadline (jobs j') < job_abs_deadline (jobs j).
  Proof.
    intros j Hchoose [j' [Hin [Hready Hlt]]].
    pose proof (choose_some_implies_min_deadline j j' Hchoose Hin Hready) as Hle.
    lia.
  Qed.

  (* C2: if a ready candidate has deadline <= chosen deadline, they are equal. *)
  Lemma choose_some_tie_deadline :
      forall j j',
        spec.(choose) jobs m sched t candidates = Some j ->
        In j' candidates ->
        ready jobs m sched j' t ->
        job_abs_deadline (jobs j') <= job_abs_deadline (jobs j) ->
        job_abs_deadline (jobs j) = job_abs_deadline (jobs j').
  Proof.
    intros j j' Hchoose Hin Hready Hle.
    pose proof (choose_some_implies_min_deadline j j' Hchoose Hin Hready) as Hle2.
    lia.
  Qed.

  (* ===== D. Derived Consequences ===== *)

  (* D1: the chosen job's release time is at most t. *)
  Lemma choose_some_not_running_before_release :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
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
        spec.(choose) jobs m sched t candidates = Some j ->
        0 < job_cost (jobs j).
  Proof.
    intros Hvj j _Hchoose.
    exact (Hvj j).
  Qed.

  (* ===== E. Membership Lemmas ===== *)
  (* Consequences of the choose_in_candidates spec field. *)

  (* E1: the chosen job is always in the candidate list. *)
  Lemma choose_some_implies_in_candidates :
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        In j candidates.
  Proof.
    intros j H.
    exact (spec.(choose_in_candidates) jobs m sched t candidates j H).
  Qed.

  (* E2: if a ready candidate exists, choose does not return None. *)
  Lemma exists_ready_candidate_implies_not_none :
      (exists j, In j candidates /\ ready jobs m sched j t) ->
      spec.(choose) jobs m sched t candidates <> None.
  Proof.
    intros Hex Hnone.
    destruct (ready_exists_implies_choose_some Hex) as [j' Hj'].
    rewrite Hnone in Hj'. discriminate.
  Qed.

  (* E3: if choose returns None, each candidate is either unreleased, completed,
     or currently running on some CPU.
     (ready = eligible AND NOT running = (released AND NOT completed) AND NOT running,
      NOT ready means NOT eligible OR running, i.e., unreleased OR completed OR running.) *)
  Lemma choose_none_implies_each_candidate_unreleased_or_completed :
      spec.(choose) jobs m sched t candidates = None ->
      forall j, In j candidates ->
        ~released jobs j t \/ completed jobs m sched j t \/ running sched m j t.
  Proof.
    intros Hnone j Hin.
    pose proof (choose_none_implies_no_ready Hnone j Hin) as Hnready.
    unfold ready, eligible in Hnready.
    destruct (classic (released jobs j t)) as [Hrel | Hnrel].
    - destruct (classic (running sched m j t)) as [Hrun | Hnrun].
      + right. right. exact Hrun.
      + right. left. apply NNPP. intro Hnc. apply Hnready.
        split. split. exact Hrel. exact Hnc. exact Hnrun.
    - left. exact Hnrel.
  Qed.

  (* ===== F. Coverage Lemmas ===== *)
  (* Lemmas parametrised over the coverage predicates defined above. *)

  (* F3: under sound candidates, the chosen job is in the list and ready. *)
  Lemma choose_some_under_sound_candidates :
      candidates_sound jobs m sched t candidates ->
      forall j,
        spec.(choose) jobs m sched t candidates = Some j ->
        In j candidates /\ ready jobs m sched j t.
  Proof.
    intros Hsound j Hchoose.
    split.
    - exact (choose_some_implies_in_candidates j Hchoose).
    - exact (choose_some_implies_ready j Hchoose).
  Qed.

  (* F4: under complete candidates, any ready job implies choose returns Some. *)
  Lemma choose_some_if_any_ready_under_complete_candidates :
      candidates_complete jobs m sched t candidates ->
      (exists j, ready jobs m sched j t) ->
      exists j', spec.(choose) jobs m sched t candidates = Some j'.
  Proof.
    intros Hcomplete [j Hready].
    apply ready_exists_implies_choose_some.
    exists j. split.
    - apply Hcomplete. exact Hready.
    - exact Hready.
  Qed.

End UniSchedulerLemmasSection.
