---

# D-2 実装 plan

## 方針

D-2 は新基礎を一から作る phase ではない。
現実装にはすでに

* migration-aware service 分解
* completion/service bridge
* remaining cost の multicore step lemma
* laxity の multicore step lemma

が入っている。したがって D-2 の主眼は、**これらを public semantic invariant として再整理し、Phase H/J の client が直に使える theorem inventory にすること**である。roadmap 上の D の残件とも一致する。

また、D-2 では **analysis layer の list-based coverage (`covers_running_jobs`) を Common 側へ持ち込まない** 方がよい。
D-2 Common で固定すべき「running set coverage」は、list coverage ではなく **set-level の `running_set_at ⊆ S` / `top_m_selected_from` の pointwise consequence** である。list coverage は後で `Analysis/Multicore/Interference.v` が消費すればよい。

---

## D-2a. 層逆転の解消

**実装ファイル**

* `theories/Multicore/Common/ServiceFacts.v`
* `theories/Analysis/Multicore/ProcessorSupply.v`

**TODO**

* `total_cpu_service_at`
* `cumulative_total_cpu_service`
* `total_cpu_service_between`
* それらの purely semantic な基本補題

  * `total_cpu_service_at_le_num_cpus`
  * `total_cpu_service_between_split`
  * `total_cpu_service_between_single_slot`
    を `ProcessorSupply.v` から `ServiceFacts.v` へ移す、または `Multicore/Common` 側の新 section に吸収する
* `ProcessorSupply.v` は以後、

  * capacity equality
  * capacity upper bound
  * all-cpus-busy からの供給系定理
    だけを残す

**完了条件**

* `Multicore/Common/*` が `Analysis/*` を import しない
* `ProcessorSupply.v` が `ServiceFacts.v` を import する片方向依存になる

---

## D-2b. `ServiceFacts.v` の public semantic invariant 化

**実装ファイル**

* `theories/Multicore/Common/ServiceFacts.v`

**現状**
既に次がある。

* `service_sum_on_cpus`
* `service_job_eq_sum_of_cpu_services`
* `service_between_eq_sum_of_cpu_services`
* `service_sum_on_cpus_step`
* `no_duplication_service_sum_step_le_1`
* `service_between_le_total_cpu_service_between`
* `no_duplication_service_between_le_interval_length`

**追加 TODO**

* public inventory comment を追加する
* migration-aware decomposition の canonical theorem を明示する

  * `service_job_eq_sum_of_cpu_services`
  * `service_between_eq_sum_of_cpu_services`
* monotonicity を明示する

  * `service_sum_on_cpus_monotone`
  * `service_between_nonnegative` は不要
* one-step upper-bound theorem を client-friendly にする

  * 既存 `no_duplication_service_sum_step_le_1` を canonical のまま残す
  * 必要なら別名 wrapper を追加する
* `machine_full_at` と machine supply の pointwise bridge を追加する

  * `machine_full_at_implies_total_cpu_service_at_eq_m`
  * 必要なら逆向き `total_cpu_service_at_eq_m_implies_machine_full_at`

**推奨追加 lemma**

```coq id="vjlwm2"
Lemma service_sum_on_cpus_monotone :
  forall m sched j t1 t2,
    t1 <= t2 ->
    service_sum_on_cpus m sched j t1 <= service_sum_on_cpus m sched j t2.
```

```coq id="gbgsvu"
Lemma machine_full_at_implies_total_cpu_service_at_eq_m :
  forall m sched t,
    machine_full_at m sched t ->
    total_cpu_service_at m sched t = m.
```

**注意**
D-2 の「running set coverage lemma」はここで list coverage を定義しない。
ここでは **pointwise な `machine_full_at` / `running_set_at` / `service` の橋**までで止める。

---

## D-2c. `CompletionFacts.v` の標準 machine-full consequence 整理

**実装ファイル**

* `theories/Multicore/Common/CompletionFacts.v`

**現状**
既に次がある。

* `completed_iff_service_sum_ge_cost`
* `not_completed_iff_service_sum_lt_cost`
* `eligible_iff_released_and_service_sum_lt_cost`
* `valid_running_implies_service_sum_lt_cost`
* `valid_no_duplication_service_sum_le_cost`
* `valid_no_duplication_service_between_le_cost`

**追加 TODO**

* `TopMAdmissibilityBridge.v` を import する
* D-1 の `top_m_selected_from` から、**ready/eligible だが non-running な job は machine-full を強制する**標準補題を追加する
* admissibility-aware 版も strong spec 側で平行に追加する

**推奨追加 lemma**

```coq id="46g4jz"
Lemma top_m_selected_from_missing_subset_eligible_implies_machine_full :
  forall J jobs m sched t j,
    top_m_selected_from (subset_eligible_at J jobs m sched t) m sched t ->
    J j ->
    eligible jobs m sched j t ->
    ~ running m sched j t ->
    machine_full_at m sched t.
Proof.
  intros J jobs m sched t j Hsel HJ Helig Hnrun.
  eapply top_m_selected_missing_implies_machine_full; eauto.
  exact (conj HJ Helig).
Qed.
```

```coq id="mr7g7v"
Lemma top_m_selected_from_missing_subset_admissible_somewhere_implies_machine_full :
  forall adm J jobs m sched t j,
    top_m_selected_from (subset_admissible_somewhere_at adm J jobs m sched t) m sched t ->
    J j ->
    admissible_somewhere adm jobs m sched j t ->
    ~ running m sched j t ->
    machine_full_at m sched t.
```

**狙い**
Phase H/J で projection 後に得るのは典型的に

* `eligible jobs m sched j t`
* `~ running m sched j t`

である。そこから **直ちに machine-full** を出せる public lemma をここで揃える。

---

## D-2d. `RemainingCostFacts.v` の one-step change 整理

**実装ファイル**

* `theories/Multicore/Common/RemainingCostFacts.v`

**現状**
既に次がある。

* `remaining_cost_eq_job_cost_minus_service_sum`
* `remaining_cost_step_running_mc`
* `remaining_cost_step_not_running_mc`

**追加 TODO**

* running / not-running の case lemma はそのまま残す
* interval client が case split なしで使える **step-bound lemma** を追加する
* monotonicity を追加する

**推奨追加 lemma**

```coq id="7if4bk"
Lemma remaining_cost_step_bounds_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    remaining_cost jobs m sched j (S t) <= remaining_cost jobs m sched j t /\
    remaining_cost jobs m sched j t <= S (remaining_cost jobs m sched j (S t)).
```

```coq id="d33lwy"
Lemma remaining_cost_monotone_mc :
  forall jobs m sched j t1 t2,
    no_duplication m sched ->
    t1 <= t2 ->
    remaining_cost jobs m sched j t2 <= remaining_cost jobs m sched j t1.
```

**狙い**
`remaining_cost_step_running_mc` / `...not_running...` は局所証明にはよいが、interval client には使いにくい。
D-2 では **「1 ステップで高々 1 だけ減る」** という形へ持ち上げる。

---

## D-2e. `LaxityFacts.v` の one-step change 整理

**実装ファイル**

* `theories/Multicore/Common/LaxityFacts.v`

**現状**
既に次がある。

* `laxity_unfold_service_sum`
* `laxity_step_running_mc`
* `laxity_step_not_running_mc`

**追加 TODO**

* case lemma はそのまま残す
* case split なしで使える **step-bound lemma** を追加する
* fairness client が直接使える「高々 1 だけ悪化する」形を出す

**推奨追加 lemma**

```coq id="xhwt3t"
Lemma laxity_step_bounds_mc :
  forall jobs m sched j t,
    no_duplication m sched ->
    (laxity jobs m sched j t - 1 <= laxity jobs m sched j (S t))%Z /\
    (laxity jobs m sched j (S t) <= laxity jobs m sched j t)%Z.
```

**狙い**
fairness / bounded waiting client は

* running なら laxity 不変
* non-running なら 1 減少
  を毎回場合分けしたくない。
  ここで **`[-1, 0]` の step-change bound** を用意しておく。

---

## D-2f. fairness client 向け import 群の整理

**実装ファイル**

* `theories/Multicore/Common/ServiceFacts.v`
* `theories/Multicore/Common/CompletionFacts.v`
* `theories/Multicore/Common/RemainingCostFacts.v`
* `theories/Multicore/Common/LaxityFacts.v`

**TODO**
各ファイル冒頭に `Public downstream theorems in this file:` コメントを追加し、最低でも次を明記する。

* `ServiceFacts.v`

  * migration-aware service decomposition
  * step/interval service bounds
  * machine-full と machine supply の橋
* `CompletionFacts.v`

  * completion/service equivalences
  * eligible/non-running -> machine-full
* `RemainingCostFacts.v`

  * exact running/non-running step lemmas
  * step-bound lemmas
* `LaxityFacts.v`

  * exact running/non-running step lemmas
  * step-bound lemmas

**fairness client が直接 import すべき群**

* `Multicore/Common/MultiCoreBase.v`
* `Multicore/Common/TopMAdmissibilityBridge.v`
* `Multicore/Common/ServiceFacts.v`
* `Multicore/Common/CompletionFacts.v`
* `Multicore/Common/RemainingCostFacts.v`
* `Multicore/Common/LaxityFacts.v`

この段階では **新しい entry-point file は作らなくてよい**。
D-2 では theorem inventory の明示だけで十分である。

---

# 実装順

## Step 0

`ServiceFacts.v` から `Analysis/Multicore/ProcessorSupply.v` 依存を外す

## Step 1

`ServiceFacts.v` に

* machine supply の基本定義
* `service_sum_on_cpus_monotone`
* `machine_full_at_implies_total_cpu_service_at_eq_m`
  を追加する

## Step 2

`CompletionFacts.v` に

* `top_m_selected_from_missing_subset_eligible_implies_machine_full`
* admissibility-aware 版
  を追加する

## Step 3

`RemainingCostFacts.v` に

* `remaining_cost_step_bounds_mc`
* `remaining_cost_monotone_mc`
  を追加する

## Step 4

`LaxityFacts.v` に

* `laxity_step_bounds_mc`
  を追加する

## Step 5

4ファイルの public inventory comment を整理する

軽微な注意として、`TopMAdmissibilityBridge.v` 冒頭コメントの
「generic adm busy lemma は `0 < m` 不要」
という説明と、`top_m_algorithm_some_cpu_busy_if_subset_admissible_somewhere_gen` の statement は少しずれている。これは **D-2 の blocker ではない**が、D-2 か D-3 のどこかでコメント整合は取った方がよい。

---

## Status note

D-2 のコード実装は完了済み。
残作業は `TopMAdmissibilityBridge.v` のコメント整合と、関連する
`plan/` / `design/` ドキュメントの inventory 同期に限定する。
