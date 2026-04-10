# Partitioned schedule composition layer

狙いは、

* 各 CPU ごとの single-CPU witness schedule から
* 1 本の global partitioned schedule を構成し
* `partitioned_scheduler ...` の witness にする

ことです。

このタスクが終わると、すぐ次に

* `partitioned EDF`
* `partitioned FIFO`
* `partitioned RR`

を同じ枠組みで載せられます。

---

## まず作るべきファイル

いちばん自然なのは次の2ファイルです。

### 1. `theories/PartitionedCompose.v`

ここに、**local schedules を global schedule に貼り合わせる一般層**を置きます。

役割は次です。

* `glue_local_schedules` の定義
* `cpu_schedule` と glue の整合補題
* local witness 群から `partitioned_schedule_on` を作る補題
* local validity / local feasibility から global validity / feasibility を作る intro 定理

### 2. `theories/PartitionedPolicies/PartitionedEDF.v`

ここに、generic composition を **EDF に具体化した薄い wrapper** を置きます。

役割は次です。

* `partitioned_edf_scheduler`
* local EDF witness から global partitioned EDF witness を作る補題
* 将来 FIFO / RR を追加するときの雛形

---

## `_CoqProject` への追加案

```text
theories/PartitionedCompose.v
theories/PartitionedPolicies/PartitionedEDF.v
```

---

## 実装方針

### Step 1: local schedules を貼り合わせる定義を作る

まずは global schedule を定義します。

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import Partitioned.

Definition glue_local_schedules
    (m : nat)
    (locals : CPU -> Schedule) : Schedule :=
  fun t c =>
    if c <? m then locals c t 0 else None.
```

ポイントは、global 側の CPU `c` には、local schedule `locals c` の仮想 CPU 0 を置くことです。
`c >= m` は常に `None` にしておくと扱いがきれいです。

---

### Step 2: `cpu_schedule` で戻すと local に戻ることを証明する

この補題が glue の中心です。

```coq
Lemma cpu_schedule_glue_eq :
  forall m spec candidates_of jobs (locals : CPU -> Schedule) c,
    c < m ->
    scheduler_rel (single_cpu_dispatch_schedule spec candidates_of) jobs 1 (locals c) ->
    cpu_schedule (glue_local_schedules m locals) c = locals c.
Proof.
  intros m spec candidates_of jobs locals c Hc Hrel.
  extensionality t.
  extensionality cpu'.
  unfold cpu_schedule, glue_local_schedules.
  destruct (Nat.eqb cpu' 0) eqn:E0.
  - apply Nat.eqb_eq in E0. subst cpu'.
    apply Nat.ltb_lt in Hc.
    now rewrite Hc.
  - apply Nat.eqb_neq in E0.
    destruct Hrel as [_ Hsteps].
    destruct (Hsteps t) as [_ Hidle].
    specialize (Hidle cpu').
    destruct (c <? m) eqn:Ec.
    + exact (Hidle (Nat.lt_gt_cases 0 cpu' |> proj2)).
    + apply Nat.ltb_ge in Ec. lia.
Qed.
```

実際には最後の `0 < cpu'` の与え方を少し整える必要がありますが、骨格はこれです。

---

### Step 3: local bridge relation から `partitioned_schedule_on` を作る

`Partitioned.v` にはすでに

* `partitioned_schedule_on_iff_local_rel`

があるので、これを使うのが最短です。

狙う補題はこれです。

```coq
Theorem glue_local_rels_imply_partitioned_schedule_on :
  forall (assign : JobId -> CPU) (m : nat)
         (valid_assignment : forall j, assign j < m)
         (spec : GenericDispatchSpec)
         (J : JobId -> Prop) (enumJ : list JobId)
         (enumJ_complete : forall j, J j -> In j enumJ)
         (enumJ_sound : forall j, In j enumJ -> J j)
         jobs (locals : CPU -> Schedule),
    (forall c, c < m ->
      scheduler_rel
        (single_cpu_dispatch_schedule spec
           (local_candidates_of assign m valid_assignment spec J enumJ c))
        jobs 1 (locals c)) ->
    partitioned_schedule_on assign m valid_assignment spec J enumJ jobs
      (glue_local_schedules m locals).
```

証明の流れは単純です。

1. `partitioned_schedule_on_iff_local_rel` を使う
2. 各 `c < m` について `cpu_schedule (glue ...) c = locals c` を示す
3. その等式で local relation を書き換える

---

### Step 4: local witness 群から global `schedulable_by_on` を作る intro 定理を作る

ここがこのタスクの到達点です。

最初は **「各 CPU について explicit な witness schedule が与えられている」形** にするのがよいです。
`forall c, exists sched_c, ...` からすぐ一般定理にすると、constructive choice が入って重くなります。

最初の到達定理はこれです。

```coq
Theorem local_witnesses_imply_partitioned_schedulable_by_on :
  forall (assign : JobId -> CPU) (m : nat)
         (valid_assignment : forall j, assign j < m)
         (spec : GenericDispatchSpec)
         (J : JobId -> Prop) (enumJ : list JobId)
         (enumJ_complete : forall j, J j -> In j enumJ)
         (enumJ_sound : forall j, In j enumJ -> J j)
         jobs (locals : CPU -> Schedule),
    (forall c, c < m ->
      scheduler_rel
        (single_cpu_dispatch_schedule spec
           (local_candidates_of assign m valid_assignment spec J enumJ c))
        jobs 1 (locals c) /\
      valid_schedule jobs 1 (locals c) /\
      feasible_schedule_on
        (fun j => J j /\ assign j = c) jobs 1 (locals c)) ->
    schedulable_by_on J
      (partitioned_scheduler assign m spec enumJ) jobs m.
Proof.
  intros assign m valid_assignment spec J enumJ enumJ_complete enumJ_sound
         jobs locals Hlocals.
  set (sched := glue_local_schedules m locals).

  assert (Hrel :
    scheduler_rel (partitioned_scheduler assign m spec enumJ) jobs m sched).
  { ... }

  assert (Hvalid : valid_schedule jobs m sched).
  { ... }

  assert (Hfeas : feasible_schedule_on J jobs m sched).
  { ... }

  exact (partitioned_schedulable_by_on_intro
           assign m spec J enumJ jobs sched Hrel Hvalid Hfeas).
Qed.
```

ここで `Hvalid` と `Hfeas` は、すでにある補題をかなりそのまま再利用できます。

* `partitioned_schedule_implies_valid_schedule`
* `local_feasible_on_implies_global_feasible_on`
* `local_valid_feasible_on_implies_global`

---

## その次に作る具体化ファイル

### `theories/PartitionedPolicies/PartitionedEDF.v`

これはかなり薄くてよいです。

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import DispatchInterface.
Require Import DispatchSchedulerBridge.
Require Import Partitioned.
Require Import PartitionedCompose.
Require Import UniPolicies.EDF.

Definition partitioned_edf_scheduler
    (assign : JobId -> CPU)
    (m : nat)
    (enumJ : list JobId)
    : Scheduler :=
  partitioned_scheduler assign m edf_generic_spec enumJ.
```

続いて、EDF 専用の intro を置きます。

```coq
Theorem local_edf_witnesses_imply_partitioned_edf_schedulable_by_on :
  forall (assign : JobId -> CPU) (m : nat)
         (valid_assignment : forall j, assign j < m)
         (J : JobId -> Prop) (enumJ : list JobId)
         (enumJ_complete : forall j, J j -> In j enumJ)
         (enumJ_sound : forall j, In j enumJ -> J j)
         jobs (locals : CPU -> Schedule),
    (forall c, c < m ->
      scheduler_rel
        (edf_scheduler
           (local_candidates_of assign m valid_assignment edf_generic_spec J enumJ c))
        jobs 1 (locals c) /\
      valid_schedule jobs 1 (locals c) /\
      feasible_schedule_on
        (fun j => J j /\ assign j = c) jobs 1 (locals c)) ->
    schedulable_by_on J
      (partitioned_edf_scheduler assign m enumJ) jobs m.
Proof.
  ...
Qed.
```

この定理ができると、次に FIFO 版をほぼ同形で追加できます。

---

## このタスクであえてやらないこと

今回のバッチでは、次は入れないのが安全です。

* global EDF
* multicore work-conserving の一般定義
* migration / IPI / OS operational semantics
* `forall c, exists sched_c` からの一般的 choice 補題

最後の choice 補題は後で別ファイルに切るのがよいです。
まず explicit `locals : CPU -> Schedule` 版を完成させると、構成がかなり見えやすくなります。

---

## 作業順

実際の作業順はこれがよいです。

1. `PartitionedCompose.v` を作る
2. `glue_local_schedules` を定義する
3. `cpu_schedule_glue_eq` を証明する
4. `glue_local_rels_imply_partitioned_schedule_on` を証明する
5. `local_witnesses_imply_partitioned_schedulable_by_on` を証明する
6. `PartitionedPolicies/PartitionedEDF.v` を作る
7. EDF 専用 wrapper と intro theorem を置く
8. `SchedulableExamples.v` に小さな partitioned EDF 例を追加する
