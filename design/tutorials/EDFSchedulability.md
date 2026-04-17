# Tutorial: Many-Task EDF Schedulability With Obligation Packages

This note documents the checked tutorial in:

* `Tutorials/EDFSchedulability.v`

There is only one EDF tutorial. It is the many-task finite-horizon tutorial,
and it uses the package-based generated-EDF analysis flow.

---

## 1. Goal

The tutorial proves schedulability of a concrete zero-offset periodic task set
under generated EDF on one processor over a finite horizon.

It presents two theorem applications:

* first choice: classical DBF package
* fallback: window-DBF package

The checked final theorems are:

```coq
Theorem tutorial_many_task_schedulable_by_classical_package_on_finite_horizon : ...

Theorem tutorial_many_task_schedulable_by_window_package_on_finite_horizon : ...
```

The classical-DBF path is the preferred entry point for zero-offset concrete
task sets.

---

## 2. Concrete Model

The tutorial defines:

* three periodic tasks,
* zero offsets,
* a finite horizon `H_many = 5`,
* three in-horizon jobs, one per task,
* a default out-of-scope job.

All task periods are larger than the horizon, so only the `0`-th job of each
task appears in the finite-horizon job set. This keeps the example concrete
while still being a genuine many-task example.

---

## 3. Finite-Horizon Codec

The tutorial builds a concrete `PeriodicFiniteHorizonCodec`:

* `job_id_many`
* `codec_many_sound`
* `codec_many_complete`
* `finite_codec_many`

Because each in-horizon task contributes only one job, the codec maps task IDs
`0`, `1`, and `2` directly to job IDs `0`, `1`, and `2`.

This is the concrete encoding layer between periodic task releases and the
finite job enumeration used by generated EDF.

---

## 4. Checker Results

The tutorial computes the two boolean obligations that drive the packaged flow:

```coq
Example many_task_window_dbf_test :
  window_dbf_test_upto tasks_many offset_many enumT_many H_many = true.

Example many_task_dbf_test_by_cutoff :
  dbf_test_by_cutoff tasks_many enumT_many = true.
```

These are the computational entry points.

* `window_dbf_test_upto = true` supports the window-DBF package
* `dbf_test_by_cutoff = true` supports the classical-DBF package

---

## 5. No-Carry-In Bridge

The schedule-side bridge is packaged per job in:

```coq
Lemma many_task_deadline_and_no_carry_in : ...
```

In this tutorial, every in-horizon job has release time `0`, so the
no-carry-in bridge is discharged by the generic lemma:

```coq
periodic_edf_busy_prefix_no_carry_in_if_release_zero
```

This is the structural side of the proof. No ad hoc job-by-job busy-prefix
enumeration is needed.

---

## 6. Obligation Packages

The tutorial assembles the full finite-horizon obligations into two records:

```coq
Definition many_task_window_obligations :
  PeriodicEDFConcreteWindowObligations ...

Definition many_task_classical_obligations :
  PeriodicEDFConcreteClassicalObligations ...
```

These packages gather:

* well-formed tasks,
* task enumeration soundness and completeness,
* checker success,
* per-job horizon/deadline facts,
* per-job no-carry-in bridge facts.

This is the canonical finite generated-EDF assembly point for concrete many-task
examples.

---

## 7. Final Theorem Applications

The tutorial applies the package-facing wrappers exported by
`PeriodicEDFAnalysisEntryPoints`.

### 7.1 First choice: classical DBF

```coq
Theorem tutorial_many_task_schedulable_by_classical_package_on_finite_horizon :
  schedulable_by_on ...
Proof.
  apply periodic_edf_schedulable_by_classical_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_classical_obligations.
Qed.
```

### 7.2 Fallback: window DBF

```coq
Theorem tutorial_many_task_schedulable_by_window_package_on_finite_horizon :
  schedulable_by_on ...
Proof.
  apply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_window_obligations.
Qed.
```

The intended reading order is:

1. compute checker results,
2. build the no-carry-in bridge,
3. package the obligations,
4. apply the classical-DBF wrapper first,
5. fall back to the window-DBF wrapper if needed.

---

## 8. Tutorial Pattern

The tutorial establishes the repository’s standard many-task proof pattern:

* compute DBF obligations,
* avoid full schedule expansion,
* discharge schedule-side obligations structurally,
* package the concrete facts,
* apply a generated-EDF entry point.

For zero-offset periodic task sets, the preferred entry point is the
classical-DBF package wrapper.
