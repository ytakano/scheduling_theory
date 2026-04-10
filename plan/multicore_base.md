# `MultiCoreBase.v` の導入

## 目標

`MultiCoreBase.v` の役割は次の3つに限定します。

1. `Partitioned` に依存しない **multicore 共通定義** を置く
2. `ScheduleModel` にすでにある基盤と整合する **薄いラッパー / bridge** を置く
3. 将来の `GlobalSchedulerInterface.v` や `OS semantics` から再利用できる形にする

ここで重要なのは、**最初の導入では意味を増やしすぎない**ことです。
特に `work-conserving` は partitioned/global で定義が分かれるので、`MultiCoreBase.v` の第1版にはまだ入れない方が安全です。`what_to_prove.md` でも、multicore 共通性質として `no-duplication / one-copy / determinism / work-conserving` は次段の整理対象になっています。

---

## 設計方針

### 1. `sequential_jobs` をすぐ消さない

現状の `ScheduleModel.v` / `ScheduleFacts.v` は `sequential_jobs` を中心に補題が積まれています。
したがって、第1段階では

```coq
Definition no_duplication (m : nat) (sched : Schedule) : Prop :=
  sequential_jobs m sched.
```

という **別名** にして、以後の multicore 側の新しい記述は `no_duplication` を使う、という方針がよいです。

これで、

* 既存補題を壊さない
* roadmap の語彙に合わせられる
* DAG 導入時に `sequential_jobs` から node-level へ移る橋頭堡になる

という利点があります。DAG では `same job not duplicated` を `same node not duplicated` へ置き換える構想なので、名前の分離は今のうちにやっておく価値があります。

### 2. `cpu_schedule` は `Partitioned.v` から移す

`cpu_schedule` は assignment に依存しない純粋な「global schedule の CPU c 視点」なので、`Partitioned.v` ではなく `MultiCoreBase.v` に置くのが自然です。
これは将来 `global` や `trace semantics` でも再利用しやすいです。

### 3. `glue_local_schedules` は移さない

これは multicore 一般論ではなく、**partitioned composition そのもの**なので `PartitionedCompose.v` に残すのがよいです。

---

## 作るべき `MultiCoreBase.v` の骨子

最初の版は次のくらいがちょうどよいです。

```coq
From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
Require Import Base.
Require Import ScheduleModel.
Require Import ScheduleLemmas.ScheduleFacts.

(* ===== Multicore common definitions ===== *)

(* Global schedule restricted to CPU c, seen as a 1-CPU schedule on virtual CPU 0. *)
Definition cpu_schedule (sched : Schedule) (c : CPU) : Schedule :=
  fun t cpu' => if Nat.eqb cpu' 0 then sched t c else None.

(* Preferred multicore name; keep compatibility with existing ScheduleModel. *)
Definition no_duplication (m : nat) (sched : Schedule) : Prop :=
  sequential_jobs m sched.

Definition cpu_idle (sched : Schedule) (t : Time) (c : CPU) : Prop :=
  sched t c = None.

Definition cpu_busy (sched : Schedule) (t : Time) (c : CPU) : Prop :=
  exists j, sched t c = Some j.

Definition all_cpus_idle (m : nat) (sched : Schedule) (t : Time) : Prop :=
  forall c, c < m -> cpu_idle sched t c.

Definition some_cpu_idle (m : nat) (sched : Schedule) (t : Time) : Prop :=
  exists c, c < m /\ cpu_idle sched t c.

Definition globally_runnable
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time) : Prop :=
  exists j, eligible jobs m sched j t.

(* Optional forward-compatible hook for affinity/global WC later. *)
Definition admissible_cpu := JobId -> CPU -> Prop.

Definition runnable_on_cpu
    (adm : admissible_cpu)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) (c : CPU) : Prop :=
  c < m /\ adm j c /\ eligible jobs m sched j t.
```

---

## このファイルに入れる補題の順序

補題は、最初から多く入れず、**依存順に一直線**で積むのがよいです。

### A. `cpu_schedule` 基本補題

まずは view 変換の基本だけ置きます。

```coq
Lemma cpu_schedule_eq_cpu0 :
  forall sched c t,
    cpu_schedule sched c t 0 = sched t c.

Lemma cpu_schedule_idle_other_cpus :
  forall sched c t cpu',
    0 < cpu' ->
    cpu_schedule sched c t cpu' = None.

Lemma runs_on_cpu_schedule :
  forall sched c j t,
    runs_on (cpu_schedule sched c) j t 0 = runs_on sched j t c.
```

必要なら次も入れてよいです。

```coq
Lemma running_on_cpu_schedule_iff :
  forall sched c j t,
    running 1 (cpu_schedule sched c) j t <-> sched t c = Some j.
```

ただしこれは `running` の展開が少し煩雑なので、第1版では後回しでも構いません。

### B. `no_duplication` bridge 補題

既存の `sequential_jobs` ベース補題を再利用するための橋を置きます。

```coq
Lemma no_duplication_iff_sequential_jobs :
  forall m sched,
    no_duplication m sched <-> sequential_jobs m sched.
```

これは定義が alias なら `tauto` で済みます。

### C. `cpu_count` 系の multicore 呼び名補題

新規証明はほぼ不要で、`ScheduleFacts` の既存補題を貼り直します。

```coq
Lemma no_duplication_cpu_count_le_1 :
  forall m sched j t,
    no_duplication m sched ->
    cpu_count m sched j t <= 1.

Lemma no_duplication_cpu_count_0_or_1 :
  forall m sched j t,
    no_duplication m sched ->
    cpu_count m sched j t = 0 \/ cpu_count m sched j t = 1.

Lemma no_duplication_cpu_count_eq_1_iff_executed :
  forall m sched j t,
    no_duplication m sched ->
    (cpu_count m sched j t = 1 <->
     exists c, c < m /\ sched t c = Some j).
```

これらは中身を再証明せず、`cpu_count_le_1` などへ流すだけでよいです。

### D. idle / busy 補題

これも軽いものだけで十分です。

```coq
Lemma cpu_idle_iff_not_busy :
  forall sched t c,
    cpu_idle sched t c <-> ~ cpu_busy sched t c.

Lemma all_cpus_idle_implies_not_running :
  forall m sched j t,
    all_cpus_idle m sched t ->
    ~ running m sched j t.
```

### E. validity / runnable の接続補題

ここは将来の `work-conserving` の土台になります。

```coq
Lemma valid_running_implies_globally_runnable :
  forall jobs m sched j t,
    valid_schedule jobs m sched ->
    running m sched j t ->
    globally_runnable jobs m sched t.

Lemma globally_runnable_of_running :
  forall jobs m sched j t,
    eligible jobs m sched j t ->
    globally_runnable jobs m sched t.
```

後者は名前を `eligible_implies_globally_runnable` にしてもよいです。

---

## この段階では入れないもの

第1版では、次はまだ入れない方がよいです。

* `multicore_work_conserving`
* `deterministic`
* `allowed_cpu` を前提にした強い補題
* `top-m` 関連
* `glue_local_schedules`
* partitioned 固有の `assign` / `local_jobset`
* global scheduler 固有の ready-set

これらは roadmap 上も `MultiCoreBase` の次の段に来る内容です。`MultiCoreBase.v` 自体は **軽く、抽象的で、再利用可能** にとどめるのが正解です。

---

## 既存ファイルの変更 plan

### 1. `theories/MultiCoreBase.v` を追加

まず additive に入れます。

### 2. `_CoqProject` に追加

`Partitioned.v` より前で十分です。

おすすめ順はこうです。

```text
theories/ScheduleModel.v
theories/ScheduleLemmas/ScheduleFacts.v
theories/MultiCoreBase.v
theories/SchedulerInterface.v
...
theories/Partitioned.v
```

### 3. `Partitioned.v` を最小変更で追従

`Partitioned.v` から次を削るか、`MultiCoreBase` 由来へ置換します。

* `cpu_schedule`
* `runs_on_cpu_schedule`

また、

* `partitioned_implies_sequential`

は残してもよいですが、新しい名前として

```coq
Lemma partitioned_implies_no_duplication :
  ...
```

を追加し、旧名を alias にする方が今後きれいです。

### 4. `PartitionedCompose.v` で `cpu_schedule` の import 元を変更

`glue_local_schedules` 自体はそのままで構いません。

---

## 実装を4コミットに分ける案

一気にやるより、次の分割が安全です。

### Commit 1

`MultiCoreBase.v` 新設
内容:

* `cpu_schedule`
* `no_duplication`
* `cpu_idle` / `cpu_busy`
* `globally_runnable`
* 最小補題

この段階では **他ファイル未変更** でもよいです。

### Commit 2

`Partitioned.v` を `MultiCoreBase.v` 利用に変更

* `cpu_schedule` を削除
* `runs_on_cpu_schedule` を削除
* import 追加

### Commit 3

`no_duplication` 命名へ寄せる

* `partitioned_implies_no_duplication` を追加
* 既存 `partitioned_implies_sequential` は互換用に残す

### Commit 4

将来用の軽い runnable / idle 補題を追加

これで `GlobalSchedulerInterface.v` 着手時に土台が揃います。

---

## そのまま使える着手順

実際の作業順はこれがよいです。

1. `MultiCoreBase.v` を作る
2. `cpu_schedule` とその3補題を書く
3. `no_duplication := sequential_jobs` を入れる
4. `cpu_count` bridge 補題を書く
5. `cpu_idle / cpu_busy / globally_runnable` を入れる
6. `_CoqProject` 更新
7. `Partitioned.v` の `cpu_schedule` を置換
8. `PartitionedCompose.v` の import を直す
9. 最後に `partitioned_implies_no_duplication` を追加する

---

## 完了条件

このタスクの完了条件は次です。

* `MultiCoreBase.v` が単独で compile する
* `Partitioned.v` から `cpu_schedule` 定義が消える
* `PartitionedCompose.v` がそのまま通る
* 既存定理の statement を大きく壊さない
* 将来 `GlobalSchedulerInterface.v` から import できる

---

## 追加で入れてよいコメント

`MultiCoreBase.v` の先頭には、次の意図を書いておくと将来ぶれにくいです。

```coq
(* This file collects multicore-generic notions that are independent of
   partitioned/global policy choice.

   Scope:
   - per-CPU view of a global schedule
   - no-duplication / idle / busy / runnable-like notions
   - light bridge lemmas to ScheduleModel / ScheduleFacts

   Non-goals of this file:
   - assignment-specific partitioned reasoning
   - top-m global dispatch
   - work-conserving definitions tied to a specific admissibility model
   - operational / refinement semantics
 *)
```

これで「どこまでをこのファイルに入れるか」が明確になります。
