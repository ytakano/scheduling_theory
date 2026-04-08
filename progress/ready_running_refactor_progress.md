# Proof Progress: ready_running_refactor

## Status Overview
- Overall: Complete
- Complete Changes: 16/16
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Changes

### Schedule.v

**`running` definition** — CPU-bounded
```coq
Definition running (sched : Schedule) (m : nat) (j : JobId) (t : Time) : Prop :=
  exists c : CPU, c < m /\ sched t c = Some j.
```

**`ready` definition** — runnable AND NOT running
```coq
Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  runnable jobs m sched j t /\ ~running sched m j t.
```

**`valid_schedule` definition** — runnable-based
```coq
Definition valid_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j t c, c < m -> sched t c = Some j -> runnable jobs m sched j t.
```

**Removed**: `valid_running_implies_ready` (now false — scheduled jobs are running, hence NOT ready)

**Renamed/restated**: `ready_iff_released_and_not_completed` → `ready_iff_runnable_and_not_running`
```coq
Lemma ready_iff_runnable_and_not_running : forall jobs m sched j t,
    ready jobs m sched j t <->
    runnable jobs m sched j t /\ ~running sched m j t.
Proof. unfold ready. tauto. Qed.
```

**Added**: `runnable_iff_released_and_not_completed`
```coq
Lemma runnable_iff_released_and_not_completed : forall jobs m sched j t,
    runnable jobs m sched j t <->
    released jobs j t /\ ~completed jobs m sched j t.
Proof. unfold runnable. tauto. Qed.
```

**Added**: `ready_implies_not_running`, `running_implies_not_ready`
```coq
Lemma ready_implies_not_running : forall jobs m sched j t,
    ready jobs m sched j t -> ~running sched m j t.
Proof. unfold ready. intros jobs m sched j t [_ H]. exact H. Qed.

Lemma running_implies_not_ready : forall jobs m sched j t,
    running sched m j t -> ~ready jobs m sched j t.
Proof.
  intros jobs m sched j t Hrun Hready.
  exact (ready_implies_not_running jobs m sched j t Hready Hrun).
Qed.
```

**Updated proofs** (all compile cleanly):
- `completed_not_ready`: `[[_ Hnot] _]` pattern
- `ready_implies_released`: `proj1 (proj1 Hr)`
- `ready_implies_not_completed`: `proj2 (proj1 Hr)`
- `not_ready_before_release`: `[[Hrel _] _]` pattern
- `ready_implies_runnable`: `proj1 H`
- `pending_not_ready`: `proj1 Hready`
- `valid_no_run_before_release`: unfold `runnable` (not `ready`)
- `valid_no_run_after_completion`: unfold `runnable` (not `ready`)
- `scheduled_implies_running`: gains `m` and `c < m` arguments

### EDF.v

**`readyb` definition** — added NOT-running check
```coq
Definition readyb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                   (j : JobId) (t : Time) : bool :=
  (job_release (jobs j) <=? t) &&
  negb (job_cost (jobs j) <=? service_job m sched j t) &&
  (cpu_count sched j t m =? 0).
```

**`readyb_iff` proof** — uses `cpu_count_zero_iff_not_executed` as bridge
```coq
Proof.
  intros jobs m sched j t.
  unfold readyb, ready, runnable, running, released, completed.
  rewrite Bool.andb_true_iff, Bool.andb_true_iff, Nat.leb_le,
          Bool.negb_true_iff, Nat.eqb_eq.
  split.
  - intros [[H1 H2] H3]. split.
    + split.
      * exact H1.
      * intro Hge. apply Nat.leb_le in Hge. rewrite Hge in H2. discriminate.
    + intros [c [Hlt Hc]].
      apply (proj1 (cpu_count_zero_iff_not_executed m sched j t) H3 c Hlt).
      exact Hc.
  - intros [[H1 H2] H3]. split; [split|].
    + exact H1.
    + apply Bool.not_true_iff_false. intro H. apply Nat.leb_le in H. exact (H2 H).
    + apply (proj2 (cpu_count_zero_iff_not_executed m sched j t)).
      intros c Hlt Hc. apply H3. exists c. split. exact Hlt. exact Hc.
Qed.
```

### UniSchedulerLemmas.v

**`choose_some_implies_runnable`** — uses `ready_implies_runnable`
```coq
Proof.
  intros j Hchoose.
  apply ready_implies_runnable.
  apply choose_some_implies_ready. exact Hchoose.
Qed.
```

**`choose_none_implies_each_candidate_unreleased_or_completed`** — statement extended
```coq
Lemma choose_none_implies_each_candidate_unreleased_or_completed :
    spec.(choose) jobs m sched t candidates = None ->
    forall j, In j candidates ->
      ~released jobs j t \/ completed jobs m sched j t \/ running sched m j t.
Proof.
  intros Hnone j Hin.
  pose proof (choose_none_implies_no_ready Hnone j Hin) as Hnready.
  unfold ready, runnable in Hnready.
  destruct (classic (released jobs j t)) as [Hrel | Hnrel].
  - destruct (classic (running sched m j t)) as [Hrun | Hnrun].
    + right. right. exact Hrun.
    + right. left. apply NNPP. intro Hnc. apply Hnready.
      split; [split|]; assumption.
  - left. exact Hnrel.
Qed.
```

## Proof Attempts & Diagnostics

### `readyb_iff` — fix attempts
- Attempt 1 (2026-04-08): `intro [c [Hlt Hc]]` for `~exists c, ...` fails with syntax error.
  Fix: use `intros [c [Hlt Hc]]` (plural form).
- Attempt 2 (2026-04-08): `split; assumption` for 3-obligation goal in `choose_none_implies_each_candidate_unreleased_or_completed` fails.
  Fix: use `split; [split|]; assumption`.
