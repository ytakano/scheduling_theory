# Tutorial: A Concrete Infinite-Time LLF Schedulability Proof for a Periodic Task Set

This tutorial explains, step by step, how to prove that a **concrete periodic task set** is schedulable under LLF on a **uniprocessor** using the canonical infinite-time public wrapper theorem

```coq
periodic_llf_schedulable_by_on
```

The checked Rocq code for this tutorial lives in:

* `Tutorials/LLFInfiniteSchedulability.v`

The example keeps the same spirit as the infinite EDF tutorial:

* two periodic tasks,
* zero offsets,
* one processor,
* a very small concrete model,
* and a final theorem that is compile-checked.

The main difference is that the final scheduler is now LLF, and the current LLF infinite wrapper depends on a finite-horizon bridge assumption of the form `forall H j, ...`.

---

## 1. What is the final goal?

The final theorem proves that our concrete periodic job set is schedulable by LLF on one CPU.

```coq
Theorem tutorial_periodic_llf_schedulable :
  schedulable_by_on
    (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
    (llf_scheduler
       (periodic_candidates_before
          T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
    jobs_ex 1.
```

The infinite wrapper builds a global generated LLF schedule from the released-prefix candidate source `periodic_candidates_before`. The canonical public schedulability theorem is the window-DBF wrapper, while the proof core still consumes finite-horizon bridge information.

For concrete zero-offset task sets, both infinite demand-side paths are now finite-checkable:

* the canonical window-DBF wrapper via `window_dbf_test_by_cutoff` and `window_dbf_check_by_cutoff`,
* the explicit classical-DBF convenience wrapper via `dbf_test_by_cutoff` and `dbf_check_by_cutoff`.

---

## 2. Import the required libraries

The infinite LLF tutorial needs the periodic infinite jobset, the finite-horizon predicate used in the bridge assumption, the global codec, and the stable LLF analysis entry points.

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia List Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Abstractions.Scheduler.Interface.
From RocqSched Require Import Uniprocessor.Policies.LLF.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.
From RocqSched Require Import TaskModels.Periodic.PeriodicFiniteHorizon.
From RocqSched Require Import TaskModels.Periodic.PeriodicCodec.
From RocqSched Require Import TaskModels.Periodic.PeriodicLLFAnalysisEntryPoints.
```

---

## 3. Define a concrete periodic task set

As in the EDF tutorial, we use two periodic tasks with zero offsets.

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

The finite task enumeration `enumT_ex` is still needed because the analysis counts periodic demand task-by-task. As before, what changes is not the task model, but the way jobs are represented.

---

## 4. Define an infinite family of concrete jobs

As in the EDF infinite tutorial, a `PeriodicCodec` must be total on every `(task, index)` pair.

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

This gives a canonical global naming scheme for all jobs of all in-scope tasks.

---

## 5. Show the model is well formed

We still prove the same setup facts as in the EDF tutorial:

* in-scope tasks have positive periods,
* the task enumeration is duplicate-free,
* every in-scope task is enumerated,
* every enumerated task is in scope.

These lemmas are unchanged in structure.

---

## 6. Build a global codec

The codec has the same global type as in the EDF infinite tutorial:

```coq
PeriodicCodec T_ex tasks_ex offset_ex jobs_ex
```

Soundness says that for every in-scope task `tau` and index `k`, the codec returns a job ID whose concrete job has:

* task `tau`,
* index `k`,
* a valid periodic-generation proof.

Completeness says that every job in

```coq
periodic_jobset T_ex tasks_ex offset_ex jobs_ex
```

is exactly the codec image of its own `(task, index)`.

---

## 7. Generate the infinite LLF schedule

The infinite LLF wrapper exports:

```coq
generated_periodic_llf_schedule
```

which builds the global generated LLF schedule from the released-prefix candidate source.

```coq
Definition sched_inf_ex : Schedule :=
  generated_periodic_llf_schedule
    T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex.
```

At each time `t`, the scheduler uses

```coq
periodic_candidates_before ... (S t)
```

internally, so only jobs released by time `t` matter to the LLF choice.

---

## 8. State the two remaining user obligations

The infinite LLF wrapper now leaves two analysis obligations to the user.

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

For the classical wrapper, the intended concrete proof is:

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

This helper is currently:

* scalar only,
* zero-offset only,
* conservative rather than minimal.

### 8.2 Finite busy-prefix bridge for every finite horizon

The LLF wrapper currently expects the following finite-horizon bridge:

```coq
Definition generated_edf_busy_prefix_bridge_ex : Prop :=
  forall H j,
    periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H j ->
    job_abs_deadline (jobs_ex j) <= H /\
    exists t1 t2,
      busy_prefix_witness
        (generated_periodic_edf_schedule_upto
           T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
        (job_abs_deadline (jobs_ex j)) t1 t2 /\
      periodic_edf_busy_prefix_bridge
        T_ex tasks_ex offset_ex jobs_ex
        H
        (generated_periodic_edf_schedule_upto
           T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
        j.
```

This is the key LLF-specific difference from the EDF tutorial.

The final theorem is about the infinite generated LLF schedule, but the current proof layer still consumes an EDF busy-prefix bridge over each relevant finite horizon `H`. The LLF wrapper then reuses that finite information internally.

---

## 9. Prove a no-miss theorem for one concrete job

As a first application, the tutorial proves that the first job of task `0` does not miss its deadline.

```coq
Theorem tutorial_periodic_llf_job0_no_deadline_miss :
  ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
```

The proof uses:

```coq
periodic_llf_no_deadline_miss_from_window_dbf
```

and supplies:

* the task-setup lemmas,
* the concrete proof that `(task 0, index 0)` belongs to `periodic_jobset`,
* the finite-horizon bridge hypothesis,
* the window-DBF hypothesis.

---

## 10. Apply the canonical global schedulability theorem

The final theorem follows directly from the infinite LLF wrapper:

```coq
Theorem tutorial_periodic_llf_schedulable :
  schedulable_by_on
    (periodic_jobset T_ex tasks_ex offset_ex jobs_ex)
    (llf_scheduler
       (periodic_candidates_before
          T_ex tasks_ex offset_ex jobs_ex enumT_ex codec_ex))
    jobs_ex 1.
Proof.
  eapply periodic_llf_schedulable_by_on; eauto.
  - exact Hdbf.
Qed.
```

At this point, the proof pattern is visible:

1. define the concrete periodic tasks,
2. define a truly global concrete job map,
3. prove the global codec,
4. derive the infinite window-DBF obligation from a finite cutoff check and isolate the finite-horizon busy-prefix obligation,
5. apply the canonical infinite-time LLF wrapper theorem.

The tutorial file also includes the explicit classical-DBF LLF theorem, which uses the cutoff-derived scalar DBF lemma instead of a manual `forall t` assumption.

---

## 11. What the user still has to prove

The tutorial intentionally leaves exactly one open assumption.

### Obligation: finite busy-prefix bridge for each finite horizon

You must prove:

```coq
forall H j,
  periodic_jobset_upto T_ex tasks_ex offset_ex jobs_ex H j ->
  job_abs_deadline (jobs_ex j) <= H /\
  exists t1 t2,
    busy_prefix_witness
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      (job_abs_deadline (jobs_ex j)) t1 t2 /\
    periodic_edf_busy_prefix_bridge
      T_ex tasks_ex offset_ex jobs_ex
      H
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex H enumT_ex codec_ex)
      j
```

For both the window-DBF path and the classical path, the infinite demand-side theorem is now recovered from a finite cutoff computation, so only the finite-horizon EDF busy-prefix bridge remains as a hypothesis.

---

## 12. How this differs from the EDF infinite tutorial

The EDF and LLF infinite tutorials share the same concrete model and the same global codec pattern, but they differ in one important way.

### EDF infinite tutorial

* final scheduler: EDF
* bridge assumption: specialized at each job deadline successor
* wrapper theorem consumes a per-job finite EDF bridge

### LLF infinite tutorial

* final scheduler: LLF
* bridge assumption: `forall H j`
* wrapper theorem consumes a finite-horizon EDF busy-prefix bridge uniformly across horizons

### Shared proof core

The infinite LLF wrapper does **not** replace the finite bridge layer. It builds on it.

This is the intended layering of the library:

* finite generated EDF/LLF bridge facts remain the proof core,
* infinite periodic LLF API is a wrapper above them,
* downstream users import only the stable public entry points.

As in the EDF tutorial, the concrete zero-offset example now has finite cutoff helpers for both scalar DBF and window DBF. A generic-offset infinite `window_dbf` cutoff API remains future work.
