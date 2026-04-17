# Tutorial: A Concrete Infinite-Time EDF Schedulability Proof for a Periodic Task Set

This tutorial explains, step by step, how to prove that a **concrete periodic task set** is schedulable under EDF on a **uniprocessor** using the canonical infinite-time concrete package wrapper

```coq
periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations
```

The checked Rocq code for this tutorial lives in:

* `Tutorials/EDFInfiniteSchedulability.v`

The example keeps the same spirit as the finite tutorial:

* two periodic tasks,
* zero offsets,
* one processor,
* a very small concrete model,
* and a final theorem that is compile-checked.

The main difference is that the job set is now **horizon-free**. Instead of
encoding only the jobs released before some fixed `H`, we use the global
canonical job map `canonical_periodic_jobs_from_enumT`, build the corresponding
`PeriodicCodec`, and then apply the infinite package wrapper.

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

The infinite package wrapper builds a global generated EDF schedule from the
released-prefix candidate source `periodic_candidates_before`. It discharges the
classical-DBF side from `dbf_test_by_cutoff = true`, but it does **not** remove
the finite bridge layer. The user still proves the EDF no-carry-in bridge on a
**per-job finite horizon**

```coq
S (job_abs_deadline (jobs_ex j))
```

but the public theorem itself concludes a global schedulability result.

For the concrete zero-offset example, the public package obligations are:

* task well-formedness and task enumeration facts,
* canonical global codec,
* `dbf_test_by_cutoff = true`,
* and the finite no-carry-in bridge as an external hypothesis.

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
From RocqSched Require Import TaskModels.Periodic.PeriodicClassicDBF.
From RocqSched Require Import TaskModels.Periodic.PeriodicConcreteAnalysis.
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

The finite tutorial used only the jobs released before some bounded horizon.
That is no longer enough here: a `PeriodicCodec` must be total on every
`(task, index)` pair.

The preferred infinite-time route is to reuse the canonical codec helper rather
than hand-writing a global job encoding.

```coq
Definition jobs_ex (j : JobId) : Job :=
  canonical_periodic_jobs_from_enumT tasks_ex offset_ex enumT_ex j.

Definition codec_ex :
  PeriodicCodec T_ex tasks_ex offset_ex jobs_ex :=
  zero_offset_periodic_codec_of_tasks
    T_ex tasks_ex enumT_ex
    enumT_ex_nodup
    T_ex_in_enumT_ex
    in_enumT_ex_implies_T_ex
    ltac:(vm_compute; lia).
```

This is the key design move in the current infinite tutorial. The codec is no
longer “only valid below `H`.” It now canonically names every job of every
in-scope task without exposing a custom encoding proof to downstream users.

---

## 5. Show the model is well formed

We still prove the same setup facts as in the finite tutorial:

* in-scope tasks have positive periods,
* the task enumeration is duplicate-free,
* every in-scope task is enumerated,
* every enumerated task is in scope.

These are unchanged in spirit; only the job side becomes global.

---

## 6. Build the canonical global codec

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

With the canonical helper, these codec obligations are discharged once and then
reused by the package theorem. This keeps the downstream proof focused on DBF
and the finite bridge.

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

### 8.1 Classical scalar DBF by direct proof

```coq
Lemma hyperperiod_load_ex :
  hyperperiod_load tasks_ex enumT_ex 35 = 12.
Proof.
  reflexivity.
Qed.

Lemma periodic_classical_dbf_upto_38_ex :
  forall t,
    t <= 38 ->
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  intros t Ht.
  do 39 (
    destruct t as [| t];
    [cbn; lia |]
  ).
  lia.
Qed.
```

The checked tutorial does not use `vm_compute` or cutoff booleans anymore. Instead, it proves the scalar DBF bound in two phases:

* First, it checks the concrete base interval `t <= 38` by bounded case analysis.
* Then it extends the result to all `t` using the hyperperiod `35` and the concrete load identity `hyperperiod_load ... 35 = 12`.

The resulting global scalar lemma is:

```coq
Lemma periodic_classical_dbf_from_cutoff_ex :
  forall t,
    taskset_periodic_dbf tasks_ex enumT_ex t <= t.
Proof.
  intros t.
  destruct (le_gt_dec t 38) as [Hle | Hgt].
  - exact (periodic_classical_dbf_upto_38_ex t Hle).
  - set (delta := t - 3).
    set (q := delta / 35).
    set (r := delta mod 35).
    set (base := 3 + r).
    ...
    rewrite hyperperiod_load_ex.
    nia.
Qed.
```

The arithmetic decomposition is the key infinite-time idea:

* write `t = base + q * 35`,
* keep `base` inside the finite interval `[3, 38]`,
* use `taskset_periodic_dbf_add_hyperperiod_after_deadline_n`,
* and conclude by arithmetic.

The lemma name still says `from_cutoff`, but in the checked file it is now a direct proof rather than a cutoff-check result.

### 8.1-bis Window DBF from the classical bound

The window-DBF theorem is no longer proved by a separate checker either. Instead, it is derived from the classical scalar DBF lemma using the zero-offset comparison theorem:

```coq
Lemma periodic_window_dbf_from_cutoff_ex :
  forall t1 t2,
    t1 <= t2 ->
    taskset_periodic_dbf_window tasks_ex offset_ex enumT_ex t1 t2 <= t2 - t1.
Proof.
  intros t1 t2 Hle.
  eapply Nat.le_trans.
  - eapply zero_offset_taskset_window_dbf_le_classical_dbf.
    + intros τ Hin. reflexivity.
    + intros τ Hin.
      apply tasks_ex_well_formed.
      apply enumT_ex_sound.
      exact Hin.
  - apply periodic_classical_dbf_from_cutoff_ex.
Qed.
```

This is the scalable demand-side obligation consumed by the canonical infinite-time public API. In the checked tutorial, the window bound is therefore reduced to the scalar bound instead of being established by a second boolean computation.

### 8.2 Per-job finite no-carry-in bridge

```coq
Definition generated_edf_busy_prefix_no_carry_in_bridge_ex : Prop :=
  forall j,
    periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
    periodic_edf_busy_prefix_no_carry_in_bridge
      T_ex tasks_ex offset_ex jobs_ex
      (S (job_abs_deadline (jobs_ex j)))
      (generated_periodic_edf_schedule_upto
         T_ex tasks_ex offset_ex jobs_ex
         (S (job_abs_deadline (jobs_ex j)))
         enumT_ex codec_ex)
      j.
```

This is the remaining structural point of the infinite wrapper:

* the final theorem is global,
* but the no-carry-in bridge is still supplied on the finite generated EDF schedule up to each job’s deadline successor.

Unlike the older `periodic_edf_busy_prefix_bridge`, this weaker interface does
not ask the user to prove `start_before_release` for every busy-prefix witness.
That boundary fact is derived internally from `missed_deadline` on the
generated EDF schedule; only the schedule-local no-carry-in argument remains
external.

---

## 9. Prove a no-miss theorem for one concrete job

As a first application, the tutorial proves that the first job of task `0` does not miss its deadline.

```coq
Theorem tutorial_periodic_edf_job0_no_deadline_miss :
  ~ missed_deadline jobs_ex 1 sched_inf_ex (job_id_of_ex 0 0).
```

The proof uses:

```coq
periodic_edf_no_deadline_miss_from_window_dbf_with_no_carry_in_bridge
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
  eapply periodic_edf_schedulable_by_on_with_no_carry_in_bridge.
  1: exact tasks_ex_well_formed.
  1: exact enumT_ex_nodup.
  1: exact enumT_ex_complete.
  1: exact enumT_ex_sound.
  1: apply Hbridge.
  1: exact periodic_window_dbf_from_cutoff_ex.
Qed.
```

At this point, the entire proof pattern is visible:

1. define the concrete periodic tasks,
2. instantiate the canonical global job map and codec,
3. prove `dbf_test_by_cutoff = true` or an equivalent scalar classical DBF fact,
4. isolate the finite busy-prefix obligation,
5. package the obligations and apply the canonical infinite-time EDF wrapper theorem.

The tutorial file may also include the explicit direct classical-DBF variant:

```coq
Theorem tutorial_periodic_edf_schedulable_by_classical_dbf :
  schedulable_by_on ...
```

but this direct theorem is now the lower-level path. The preferred public route
for concrete task sets is the package theorem above.

---

## 11. What the user still has to prove

The tutorial intentionally leaves exactly one non-arithmetic open assumption.

### Obligation: finite busy-prefix bridge at each job deadline

You must prove:

```coq
forall j,
  periodic_jobset T_ex tasks_ex offset_ex jobs_ex j ->
  periodic_edf_busy_prefix_no_carry_in_bridge
    T_ex tasks_ex offset_ex jobs_ex
    (S (job_abs_deadline (jobs_ex j)))
    (generated_periodic_edf_schedule_upto
       T_ex tasks_ex offset_ex jobs_ex
       (S (job_abs_deadline (jobs_ex j)))
       enumT_ex codec_ex)
    j
```

For the package route, the cutoff checker discharges the scalar classical DBF
premise automatically. The tutorial therefore leaves only the finite
no-carry-in bridge as a hypothesis.

---

## 12. How this differs from the finite tutorial

The finite tutorial and the infinite tutorial have the same high-level shape, but they differ in three important ways.

### Finite tutorial

* job set: `periodic_jobset_upto ... H_ex`
* codec: `PeriodicFiniteHorizonCodec ... H_ex`
* scheduler candidates: fixed finite list `enum_periodic_jobs_upto ... H_ex`

### Infinite tutorial

* job set: `periodic_jobset`
* codec: `PeriodicCodec`, preferably from `zero_offset_periodic_codec_of_tasks`
* scheduler candidates: released prefix `periodic_candidates_before`

### Shared proof core

The infinite wrapper does **not** replace the finite EDF bridge. It builds on it. That is why the busy-prefix bridge is still stated over the finite generated EDF schedule at each job’s deadline horizon.

This is the intended layering of the library:

* finite generated EDF bridge remains the proof core,
* infinite periodic EDF API is a wrapper above it,
* the concrete infinite package route is not bridge-free,
* downstream users import only the stable public entry points.

At the moment, the concrete zero-offset example demonstrates a different lesson from the earlier cutoff-based version: even in the infinite-time wrapper, the core proof can stay DBF-first and avoid schedule computation and boolean checker proofs entirely. A generic-offset infinite automation layer for `window_dbf` remains future work.
