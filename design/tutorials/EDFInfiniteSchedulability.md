# Tutorial: A Concrete Infinite-Time EDF Schedulability Proof for a Periodic Task Set

This tutorial explains, step by step, how to prove that a **concrete periodic task set** is schedulable under EDF on a **uniprocessor** using the canonical infinite-time public wrapper theorem

```coq
periodic_edf_schedulable_by_on
```

The checked Rocq code for this tutorial lives in:

* `Tutorials/EDFInfiniteSchedulability.v`

The example keeps the same spirit as the finite tutorial:

* two periodic tasks,
* zero offsets,
* one processor,
* a very small concrete model,
* and a final theorem that is compile-checked.

The main difference is that the job set is now **horizon-free**. Instead of encoding only the jobs released before some fixed `H`, we define a global periodic codec on `(task, index)` and use the infinite EDF wrapper.

---

## 1. What is the final goal?

The final theorem proves that our concrete periodic job set is schedulable by EDF on one CPU.

```coq
Theorem tutorial_periodic_edf_schedulable :
  schedulable_by_on
    (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
    (edf_scheduler
       (periodic_candidates_before
          T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
    jobs_ex 1.
```

The infinite wrapper builds a global generated EDF schedule from the released-prefix candidate source `periodic_candidates_before`. The canonical public schedulability theorem now consumes a window-DBF bound, while the user still proves the EDF busy-prefix bridge on a **per-job finite horizon**

```coq
S (job_abs_deadline (jobs_ex j))
```

but the public theorem itself concludes a global schedulability result.

For concrete zero-offset task sets, both infinite demand-side paths are now finite-checkable:

* the canonical window-DBF wrapper via `window_dbf_test_by_cutoff` and `window_dbf_check_by_cutoff`,
* the explicit classical-DBF convenience wrapper via `dbf_test_by_cutoff` and `dbf_check_by_cutoff`.

---

## 2. Import the required libraries

The infinite tutorial needs the periodic infinite jobset, the global codec, and the stable EDF analysis entry points.

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Uniprocessor.Policies.EDF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFAnalysisEntryPoints.
```

---

## 3. Define a concrete periodic task set

As in the finite tutorial, we use two periodic tasks with zero offsets.

```coq
Definition task0_ex : Task := mkTask 1 5 2.
Definition task1_ex : Task := mkTask 1 7 3.

Definition tasks_ex (tau : TaskId) : Task :=
  match tau with
  | 0 => task0_ex
  | 1 => task1_ex
  | _ => mkTask 1 100 100
  end.

Definition T_ex (tau : TaskId) : Prop := tau = 0 \/ tau = 1.

Definition offset_ex (_ : TaskId) : Time := 0.

Definition enumT_ex : list TaskId := [0; 1].
```

The finite task enumeration `enumT_ex` is still needed because the analysis counts periodic demand task-by-task. What changes is not the task model, but the way jobs are represented.

---

## 4. Define an infinite family of concrete jobs

The finite tutorial used only two in-scope jobs because it worked on a fixed horizon. That is no longer enough here: a `PeriodicCodec` must be total on every `(task, index)` pair.

We therefore encode:

* all jobs of task `0` as even job IDs,
* all jobs of task `1` as odd job IDs.

```coq
Definition job_id_of_ex (tau : TaskId) (k : nat) : JobId :=
  match tau with
  | 0 => 2 * k
  | 1 => S (2 * k)
  | _ => 0
  end.

Definition jobs_ex (j : JobId) : Job :=
  if Nat.even j then
    mkJob 0 (Nat.div2 j) (5 * Nat.div2 j) 1 (5 * Nat.div2 j + 2)
  else
    mkJob 1 (Nat.div2 j) (7 * Nat.div2 j) 1 (7 * Nat.div2 j + 3).
```

This is the key design move in the infinite tutorial. The codec is no longer “only valid below `H`.” It now canonically names every job of every in-scope task.

---

## 5. Show the model is well formed

We still prove the same setup facts as in the finite tutorial:

* in-scope tasks have positive periods,
* the task enumeration is duplicate-free,
* every in-scope task is enumerated,
* every enumerated task is in scope.

These are unchanged in spirit; only the job side becomes global.

---

## 6. Build a global codec

The global codec type is now:

```coq
PeriodicCodec T_ex tasks_ex offset_ex jobs_ex
```

instead of the finite-horizon type

```coq
PeriodicFiniteHorizonCodec ... H_ex
```

Soundness now says: for every in-scope task `tau` and index `k`, the codec returns a job ID whose concrete job has:

* task `tau`,
* index `k`,
* a valid periodic-generation proof.

Completeness now says: every job in

```coq
periodic_jobset T_ex tasks_ex offset_ex jobs_ex
```

is exactly the codec image of its own `(task, index)`.

This is the main proof obligation introduced by the infinite wrapper.

---

## 7. Generate the infinite EDF schedule

The infinite wrapper exports:

```coq
generated_periodic_edf_schedule
```

which builds the global EDF schedule from the released-prefix candidate source.

```coq
Definition sched_inf_ex : Schedule :=
  generated_periodic_edf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.
```

At each time `t`, the scheduler uses

```coq
periodic_candidates_before ... (S t)
```

internally, so only jobs released by time `t` are relevant to the EDF choice. The prefix-coherence proof between finite and infinite generated EDF schedules is already internalized in the library, so the tutorial does **not** assume it separately.

---

## 8. State the remaining user obligations

The infinite wrapper now leaves two analysis obligations to the user.

### 8.1 Window-DBF bound through a finite cutoff check

```coq
Example periodic_window_dbf_test_by_cutoff_ex :
  window_dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_window_dbf_from_cutoff_ex :
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  apply window_dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply enumT_ex_sound.
    exact Hin.
  - exact periodic_window_dbf_test_by_cutoff_ex.
Qed.
```

This is the scalable demand-side obligation consumed by the canonical infinite-time public API. For the concrete zero-offset example, it is now discharged by computation instead of a manual universal proof.

### 8.1-bis Classical scalar DBF through a finite cutoff check

For the classical wrapper, do **not** hand-prove

```coq
forall t, taskset_periodic_dbf tasks_ex enumT_ex t <= t
```

directly. The intended path is:

```coq
Example periodic_classical_dbf_test_by_cutoff_ex :
  dbf_test_by_cutoff tasks_ex enumT_ex = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma periodic_classical_dbf_from_cutoff_ex :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  apply dbf_check_by_cutoff.
  - exact enumT_ex_nodup.
  - intros τ Hin.
    apply tasks_ex_well_formed.
    apply enumT_ex_sound.
    exact Hin.
  - exact periodic_classical_dbf_test_by_cutoff_ex.
Qed.
```

This cutoff helper is currently:

* scalar only,
* zero-offset only,
* conservative rather than minimal.

It is meant to eliminate the user-facing infinite `forall t` proof obligation for concrete task sets.

### 8.2 Per-job finite busy-prefix bridge

```coq
Definition generated_edf_busy_prefix_bridge_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.
```

This is the structural point of the infinite wrapper:

* the final theorem is global,
* but the bridge is still supplied on the finite generated EDF schedule up to each job’s deadline successor.

The wrapper then lifts that finite information to the infinite generated EDF schedule internally.

---

## 9. Prove a no-miss theorem for one concrete job

As a first application, the tutorial proves that the first job of task `0` does not miss its deadline.

```coq
Theorem tutorial_periodic_edf_job0_no_deadline_miss :
  ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
```

The proof uses:

```coq
periodic_edf_no_deadline_miss_from_window_dbf
```

and supplies:

* the task-setup lemmas,
* the concrete proof that `(task 0, index 0)` belongs to `periodic_jobset`,
* the per-job bridge instance from the section hypothesis,
* the window-DBF hypothesis.

---

## 10. Apply the canonical global schedulability theorem

The final theorem follows directly from the infinite wrapper:

```coq
Theorem tutorial_periodic_edf_schedulable :
  schedulable_by_on
    (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
    (edf_scheduler
       (periodic_candidates_before
          T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
    jobs_ex 1.
Proof.
  eapply periodic_edf_schedulable_by_on; eauto.
  - exact Hdbf.
Qed.
```

At this point, the entire proof pattern is visible:

1. define the concrete periodic tasks,
2. define a truly global concrete job map,
3. prove the global codec,
4. derive the infinite window-DBF obligation from a finite cutoff check and isolate the busy-prefix obligation,
5. apply the canonical infinite-time EDF wrapper theorem.

The tutorial file also includes the explicit classical-DBF variant:

```coq
Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
  schedulable_by_on ...
```

which reuses `periodic_classical_dbf_from_cutoff_ex` rather than a manual universal DBF hypothesis.

---

## 11. What the user still has to prove

The tutorial intentionally leaves exactly one open assumption.

### Obligation: finite busy-prefix bridge at each job deadline

You must prove:

```coq
forall j,
  periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
  periodic_edf_busy_prefix_bridge
    T_ex tasks_ex offset_ex jobs_ex
    (S (job_abs_deadline (jobs_ex j)))
    (generated_periodic_edf_schedule_upto
       T_ex tasks_ex offset_ex jobs_ex
       (S (job_abs_deadline (jobs_ex j)))
       enumT_ex codec_ex)
    j
```

For both the window-DBF path and the classical path, the infinite demand-side theorem is now recovered from a finite cutoff computation. The tutorial therefore leaves only the busy-prefix bridge as a hypothesis.

---

## 12. How this differs from the finite tutorial

The finite tutorial and the infinite tutorial have the same high-level shape, but they differ in three important ways.

### Finite tutorial

* job set: `periodic_jobset_upto ... H_ex`
* codec: `PeriodicFiniteHorizonCodec ... H_ex`
* scheduler candidates: fixed finite list `enum_periodic_jobs_upto ... H_ex`

### Infinite tutorial

* job set: `periodic_jobset`
* codec: `PeriodicCodec`
* scheduler candidates: released prefix `periodic_candidates_before`

### Shared proof core

The infinite wrapper does **not** replace the finite EDF bridge. It builds on it. That is why the busy-prefix bridge is still stated over the finite generated EDF schedule at each job’s deadline horizon.

This is the intended layering of the library:

* finite generated EDF bridge remains the proof core,
* infinite periodic EDF API is a wrapper above it,
* downstream users import only the stable public entry points.

At the moment, the concrete zero-offset example has finite cutoff helpers for both scalar DBF and window DBF. A generic-offset infinite cutoff API for `window_dbf` remains future work.
