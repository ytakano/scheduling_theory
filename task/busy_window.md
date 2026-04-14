# Phase G-1: busy-window / busy-interval theory の導入

## ゴール

単一CPU向けに、schedule semantics の上で再利用可能な busy-window 基盤を導入する。

この段階では、いきなり EDF 専用定理まで進まず、まず以下を揃える。

1. busy interval の定義
2. busy interval の基本補題
3. interval 内 service / execution の再利用補題
4. 後続の dbf/rbf や response-time theorem に接続する形の API

---

## 実装ファイル

新規追加対象は次である。

- `theories/Analysis/Uniprocessor/BusyInterval.v`
- `theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`
- `theories/Examples/BusyIntervalExamples.v`

更新対象は次である。

- `_CoqProject`
- `plan/roadmap.md`
- `plan/what_to_prove.md`

必要なら後続で追加する。

- `theories/Analysis/Uniprocessor/BusyWindowSearch.v`

---

## TODO

### TODO 1: busy interval の最小定義を入れる
`theories/Analysis/Uniprocessor/BusyInterval.v`

まずは policy 非依存な定義だけを置く。

- `cpu_busy_at`
- `interval_busy`
- `busy_interval`
- `maximal_busy_interval_from`

ここで重要なのは、**ready queue や runqueue の operational 定義を持ち込まず**、既存の `running` / `cpu_count` / `service_job` ベースで閉じることだ。

---

### TODO 2: 基本補題を証明する
`theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`

最低限、次を揃える。

- busy interval 内では各時刻で少なくとも1 jobが実行される
- busy interval の prefix / suffix に関する補題
- busy interval 上では total service が区間長に一致する補題
- 空きスロットを含む区間は busy interval ではない補題
- maximality の分解補題

この層は後で dbf/rbf の「需要が区間長を超えるか」を扱うための土台になる。

---

### TODO 3: service 集約補題を入れる
`theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`

既存の `service_between_*` を使い、interval 上の集約を追加する。

- 区間 `[t1, t2)` における total executed service の扱い
- busy interval なら `t2 - t1` だけ processor supply があること
- 個別 job service と全体 service の接続補題

ここで multicore 一般化はまだ行わない。まず `m = 1` で API を固めるべきである。

---

### TODO 4: 小さな example を追加する
`theories/Examples/BusyIntervalExamples.v`

例として次を入れる。

- 常に何かが走っている単純 schedule が busy interval を成す例
- 途中に idle slot が入ると busy interval でない例
- periodic example の先頭区間が busy interval になる簡単な例

example を入れておくと、後段の analysis ファイルの雛形として使いやすい。

---

### TODO 5: proof inventory を更新する
`plan/what_to_prove.md`

新しい章として少なくとも次を追加する。

- Lv.9 Analysis foundations
  - busy interval definitions
  - maximal busy interval lemmas
  - interval service aggregation
  - search-space reduction hooks

これは文書更新ではあるが、実装と同時にやる価値が高い。analysis 層は API の見通しが悪くなりやすいためである。

---

## この順番にする理由

この順番にするべき理由は次の通りである。

- `periodic / sporadic / jitter` の task-generation 側はすでに finite-horizon schedulability へ接続済みである
- その次に必要なのは、別の生成モデルではなく **analysis の共通中間層** である
- utilization 定理や dbf/rbf を先に書くと、interval API が未整理のまま補題が散らばる
- busy interval を先に固定すれば、後続の
  - Liu & Layland 型補題
  - processor-demand style theorem
  - response-time search-space reduction
  に直結する

---

## Rocq スケルトン

### `theories/Analysis/Uniprocessor/BusyInterval.v`

```coq
From Stdlib Require Import Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.

Definition cpu_busy_at
    (sched : Schedule) (t : Time) : Prop :=
  exists j, sched t 0 = Some j.

Definition interval_busy
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  forall t, t1 <= t < t2 -> cpu_busy_at sched t.

Definition busy_interval
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  t1 < t2 /\
  interval_busy sched t1 t2.

Definition maximal_busy_interval_from
    (sched : Schedule) (t1 t2 : Time) : Prop :=
  busy_interval sched t1 t2 /\
  (t1 = 0 \/ ~ cpu_busy_at sched (pred t1)) /\
  ~ cpu_busy_at sched t2.
```

### `theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`

```coq
From Stdlib Require Import Arith Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Uniprocessor.BusyInterval.

Lemma busy_interval_implies_busy_at :
  forall sched t1 t2 t,
    busy_interval sched t1 t2 ->
    t1 <= t < t2 ->
    cpu_busy_at sched t.
Proof.
Admitted.

Lemma busy_interval_has_no_idle_slot :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    forall t, t1 <= t < t2 -> exists j, sched t 0 = Some j.
Proof.
Admitted.

Lemma busy_interval_total_supply_eq_length :
  forall sched t1 t2,
    busy_interval sched t1 t2 ->
    (* 後で total service 定義に合わせて整形 *)
    True.
Proof.
Admitted.
```

---

## このタスクの完了条件

完了条件は次である。

- `BusyInterval.v` に policy 非依存な定義が入る
- `BusyIntervalLemmas.v` に基本補題がまとまる
- `BusyIntervalExamples.v` に最小例が入る
- `_CoqProject` に追加される
- `what_to_prove.md` に analysis foundations の最初の棚卸しが入る
