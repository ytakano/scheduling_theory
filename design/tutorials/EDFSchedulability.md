# Tutorial: A Concrete Finite-Horizon EDF Schedulability Proof for a Many-Task Periodic Task Set

This tutorial explains, step by step, how to prove that a **concrete zero-offset
periodic task set** is schedulable under EDF on a **uniprocessor** over a
**finite horizon** using the packaged generated-EDF entry points.

The checked Rocq code for this tutorial lives in:

* `Tutorials/EDFSchedulability.v`

This is the repository's canonical finite many-task EDF tutorial. It shows the
current concrete-analysis pattern:

* define a concrete periodic task set,
* build jobs through the canonical enum-based periodic generator,
* derive a reusable global periodic codec,
* specialize it to the finite horizon,
* compute DBF checker obligations,
* discharge the remaining schedule-side bridge structurally,
* package the obligations,
* and apply the final schedulability wrappers.

Unlike older versions of this tutorial, the checked file no longer hand-writes
the job-ID codec or proves local `mod/div` codec facts by hand. It now uses
the canonical periodic codec builder from `PeriodicCodec.v`.

---

## 1. What is the final goal?

The tutorial proves schedulability of a concrete finite-horizon periodic job set
under generated EDF on one processor.

The checked final theorems are:

```coq
Theorem tutorial_many_task_schedulable_by_classical_package_on_finite_horizon :
  schedulable_by_on
    (periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many)
    (edf_scheduler
       (enum_candidates_of
          (generated_periodic_edf_finite_enumJ
             T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)))
    jobs_many 1.

Theorem tutorial_many_task_schedulable_by_window_package_on_finite_horizon :
  schedulable_by_on
    (periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many)
    (edf_scheduler
       (enum_candidates_of
          (generated_periodic_edf_finite_enumJ
             T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)))
    jobs_many 1.
```

The two theorem applications differ only in the demand-side package they use:

* the **preferred** path uses the classical scalar DBF package,
* the **fallback** path uses the explicit window-DBF package.

Both theorems conclude schedulability for the same finite-horizon generated EDF
schedule skeleton.

---

## 2. Import the required libraries

The finite tutorial needs:

* the base schedule and scheduler interfaces,
* the EDF policy,
* the periodic task model,
* the global periodic codec,
* the finite-horizon codec wrapper,
* finite periodic job enumeration,
* and the packaged EDF analysis entry points.

The checked file imports:

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Abstractions.SchedulingAlgorithm.EnumCandidates.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicEnumeration.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
```

---

## 3. Define a concrete periodic task set

The tutorial uses three zero-offset periodic tasks:

```coq
Definition task0_many : Task := mkTask 1 10 4.
Definition task1_many : Task := mkTask 1 11 4.
Definition task2_many : Task := mkTask 1 12 4.
```

They are assembled into:

```coq
Definition tasks_many (tau : TaskId) : Task := ...
Definition T_many (tau : TaskId) : Prop := tau = 0 \/ tau = 1 \/ tau = 2.
Definition offset_many (_ : TaskId) : Time := 0.
Definition H_many : Time := 5.
Definition enumT_many : list TaskId := [0; 1; 2].
```

This example is intentionally concrete:

* the horizon is `H_many = 5`,
* every task has zero offset,
* and every period is strictly larger than `5`.

As a result, only the `0`-th job of each task can appear in the finite-horizon
job set. This keeps the tutorial small while still exercising the full
many-task generated-EDF packaging flow.

---

## 4. Define concrete jobs via the canonical periodic generator

The current checked tutorial does **not** define `jobs_many` by hand using
`mod` / `div` case analysis. Instead, it uses the canonical enum-based
generator:

```coq
Definition jobs_many : JobId -> Job :=
  canonical_periodic_jobs_from_enumT tasks_many offset_many enumT_many.
```

This is the key modernization of the finite tutorial.

The intended meaning is:

* decode each `JobId` into `(position in enumT_many, k)`,
* recover the corresponding task from `enumT_many`,
* build the `k`-th periodic job of that task canonically.

For this concrete example, users no longer have to prove separate local lemmas
about how `jobs_many` behaves on IDs like `3 * k`, `S (3 * k)`, and
`S (S (3 * k))`. That arithmetic is now hidden behind the reusable codec layer.

---

## 5. Prove the setup facts

As in the infinite tutorial, we still need the standard finite task-set facts:

* in-scope tasks have positive periods,
* the task enumeration is duplicate-free,
* every in-scope task appears in the enumeration,
* every enumerated task is in scope.

The checked file packages these as:

```coq
Lemma tasks_many_well_formed :
  well_formed_periodic_tasks_on T_many tasks_many.

Lemma enumT_many_nodup :
  NoDup enumT_many.

Lemma T_many_in_enumT_many :
  forall tau, T_many tau -> In tau enumT_many.

Lemma in_enumT_many_implies_T_many :
  forall tau, In tau enumT_many -> T_many tau.
```

These are the task-side obligations consumed by the codec builder and the final
concrete EDF obligation packages.

---

## 6. Build a reusable global codec and derive the finite codec

The finite tutorial now follows the same architectural pattern as the infinite
tutorial: first build a reusable global codec, then derive the finite-horizon
specialization.

The checked code is:

```coq
Definition codec_many :
  PeriodicCodec T_many tasks_many offset_many jobs_many :=
  zero_offset_periodic_codec_of_tasks
    T_many tasks_many enumT_many
    enumT_many_nodup
    T_many_in_enumT_many
    in_enumT_many_implies_T_many
    ltac:(vm_compute; lia).

Definition finite_codec_many :
  PeriodicFiniteHorizonCodec T_many tasks_many offset_many jobs_many H_many :=
  zero_offset_periodic_finite_horizon_codec_of
    T_many tasks_many jobs_many H_many codec_many.
```

So the flow is:

1. use `zero_offset_periodic_codec_of_tasks` to build the global
   `PeriodicCodec`,
2. reuse the generic finite-horizon wrapper
   `zero_offset_periodic_finite_horizon_codec_of`,
3. avoid any hand-written `PeriodicFiniteHorizonCodec` proof.

This is the standard many-task route for concrete zero-offset periodic
instances.

---

## 7. Compute the checker results

The tutorial computes two boolean demand-side checks:

```coq
Example many_task_window_dbf_test :
  window_dbf_test_upto tasks_many offset_many enumT_many H_many = true.

Example many_task_dbf_test_by_cutoff :
  dbf_test_by_cutoff tasks_many enumT_many = true.
```

These are the two packaged analysis entry points used later:

* `window_dbf_test_upto = true` supports the window-DBF package,
* `dbf_test_by_cutoff = true` supports the classical zero-offset DBF package.

The classical path remains the preferred user-facing route for this kind of
zero-offset concrete periodic example.

---

## 8. Prove the per-job deadline and no-carry-in bridge

The main structural proof obligation in the checked file is:

```coq
Lemma many_task_deadline_and_no_carry_in :
  forall j,
    periodic_jobset_upto T_many tasks_many offset_many jobs_many H_many j ->
    job_abs_deadline (jobs_many j) <= H_many /\
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_many tasks_many offset_many jobs_many H_many
      (generated_periodic_edf_schedule_on_finite_horizon
         T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many)
      j.
```

This lemma does two things at once:

* it proves that each in-horizon generated job has deadline at most `H_many`,
* it discharges the EDF busy-prefix no-carry-in bridge required by the packaged
  finite theorem.

The proof structure is important:

1. use `periodic_job_id_of_complete` from the finite codec,
2. show that every in-horizon job has `job_index = 0`,
3. case-split on which concrete task generated the job,
4. conclude the no-carry-in bridge with
   `periodic_edf_busy_prefix_no_carry_in_if_release_zero`.

The tutorial works because every in-horizon job is the first job of its task,
hence released at time `0`.

This is exactly the kind of schedule-side argument the package interface is
meant to isolate: there is no need to enumerate full EDF prefixes manually.

---

## 9. Assemble the obligation packages

Once the task facts, boolean checks, and bridge lemma are available, the
tutorial packages them into the standard concrete obligation records.

### 9.1 Window package

```coq
Definition many_task_window_obligations :
  PeriodicEDFConcreteWindowObligations
    T_many tasks_many offset_many jobs_many H_many enumT_many finite_codec_many.
```

The record contains:

* task-set well-formedness,
* enumeration `NoDup`,
* enumeration completeness and soundness,
* the per-job deadline/no-carry-in bridge,
* the successful window DBF checker result.

### 9.2 Classical package

```coq
Definition many_task_classical_obligations :
  PeriodicEDFConcreteClassicalObligations
    T_many tasks_many jobs_many H_many enumT_many finite_codec_many.
```

This record reuses the window package as a base and adds:

* the successful classical DBF cutoff check.

This packaging step is the concrete finite-horizon assembly point for the EDF
tutorial.

---

## 10. Apply the final theorem wrappers

The final theorems consume the packaged obligations exported through
`PeriodicEDFAnalysisEntryPoints`.

### 10.1 Preferred path: classical DBF package

```coq
Theorem tutorial_many_task_schedulable_by_classical_package_on_finite_horizon :
  schedulable_by_on ...
Proof.
  apply periodic_edf_schedulable_by_classical_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_classical_obligations.
Qed.
```

This is the preferred wrapper for zero-offset concrete periodic task sets.

### 10.2 Fallback path: window-DBF package

```coq
Theorem tutorial_many_task_schedulable_by_window_package_on_finite_horizon :
  schedulable_by_on ...
Proof.
  apply periodic_edf_schedulable_by_window_dbf_on_finite_horizon_generated_from_obligations.
  exact many_task_window_obligations.
Qed.
```

This second theorem keeps the window-DBF route visible and checked, but it is
not the primary entry point for this tutorial.

---

## 11. Tutorial pattern

The checked finite tutorial now establishes the repository's standard
many-task finite-horizon EDF pattern:

1. define a concrete zero-offset periodic task set,
2. define jobs through `canonical_periodic_jobs_from_enumT`,
3. build a reusable global codec with
   `zero_offset_periodic_codec_of_tasks`,
4. derive the finite codec with
   `zero_offset_periodic_finite_horizon_codec_of`,
5. compute the demand-side DBF checks,
6. discharge the per-job schedule-side bridge structurally,
7. package the obligations,
8. apply the classical wrapper first and the window wrapper second.

This is the finite-horizon counterpart to the infinite tutorial's global
wrapper story. The main difference is that the final conclusion is restricted
to `periodic_jobset_upto ... H_many`, but the concrete modeling and codec
construction already use the same reusable global periodic infrastructure.
