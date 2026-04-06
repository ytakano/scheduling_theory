# Proof Progress: PeriodicTasks.v — 周期生成規則の骨格

## Status Overview
- Overall: Complete
- Complete Lemmas: 4/4
- Unproven (`Admitted`): none
- Failed/Abandoned Items: none

## Completed Lemmas

### `generated_job_release`

```coq
Lemma generated_job_release :
  forall tasks offset jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    job_release (jobs j) =
      expected_release tasks offset (job_task (jobs j)) (job_index (jobs j)).
Proof.
  intros tasks offset jobs j Hgen.
  exact (proj1 Hgen).
Qed.
```

### `generated_job_deadline`

```coq
Lemma generated_job_deadline :
  forall tasks offset jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    job_abs_deadline (jobs j) =
      job_release (jobs j) + task_relative_deadline (tasks (job_task (jobs j))).
Proof.
  intros tasks offset jobs j Hgen.
  destruct Hgen as [Hrel [Hdl _]].
  unfold expected_abs_deadline in Hdl.
  rewrite <- Hrel in Hdl.
  exact Hdl.
Qed.
```

### `generated_job_cost_bounded`

```coq
Lemma generated_job_cost_bounded :
  forall tasks offset jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    job_cost (jobs j) <= task_cost (tasks (job_task (jobs j))).
Proof.
  intros tasks offset jobs j Hgen.
  exact (proj2 (proj2 Hgen)).
Qed.
```

### `generated_implies_valid_job_of_task`

```coq
Lemma generated_implies_valid_job_of_task :
  forall tasks offset jobs j,
    generated_by_periodic_task tasks offset jobs j ->
    valid_job_of_task tasks jobs j.
Proof.
  intros tasks offset jobs j Hgen.
  unfold valid_job_of_task.
  split.
  - exact (generated_job_deadline tasks offset jobs j Hgen).
  - exact (generated_job_cost_bounded tasks offset jobs j Hgen).
Qed.
```

## TODO
(なし — 全補題完了)
