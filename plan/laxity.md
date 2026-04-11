
以下は、現在の実装到達点を前提にして、remaining_cost / laxity / LLF(LST) を追加するための具体的な実装 planです。
目的は、既存の
	•	ScheduleModel
	•	SchedulingAlgorithmInterface
	•	UniPolicies/EDF.v
	•	PartitionedCompose
	•	PartitionedPolicies/*

の流れを壊さずに、deadline-based の次の 1 例として laxity-based policy を自然に追加することです。

⸻

実装方針の要点

今回の追加対象は、大きく 4 層です。
	1.	共通状態量の追加
	•	remaining_cost
	•	laxity
	2.	metric-based chooser の抽象化
	•	EDF の min_dl_job を一般化して、
「候補のうち metric 最小を選ぶ」枠を作る
	3.	単一CPU LLF/LST の追加
	•	UniPolicies/Laxity.v
	4.	partitioned LLF の追加
	•	PartitionedPolicies/PartitionedLLF.v

⸻

全体の実装順

以下の順で進めるのが安全です。

Step 1

ScheduleModel.v に remaining_cost / laxity を追加

Step 2

その基本補題を ScheduleLemmas 側へ追加

Step 3

UniPolicies/MetricChooser.v を新設して EDF chooser を一般化

Step 4

UniPolicies/Laxity.v を新設して LLF/LST を実装

Step 5

PartitionedPolicies/PartitionedLLF.v を追加

Step 6

必要なら examples / progress / roadmap を更新

⸻

Step 1: ScheduleModel.v の拡張

追加先
	•	theories/ScheduleModel.v

追加する定義

1. remaining_cost

まずは job-level service に対する残作業量を入れます。

Definition remaining_cost
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : nat :=
  job_cost (jobs j) - service_job m sched j t.

これは Nat.sub なので 0 未満にはならず、完了後は 0 に潰れます。
今の completed の定義とも相性がよいです。

2. laxity

これは nat ではなく Z を推奨します。

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition laxity
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Z :=
  Z.of_nat (job_abs_deadline (jobs j))
  - Z.of_nat t
  - Z.of_nat (remaining_cost jobs m sched j t).

Z を使う理由

laxity は deadline miss 後に負になりうるため、nat にすると
	•	0-laxity
	•	negative laxity
	•	危険 job の扱い

が不自然になります。

したがって、
	•	remaining_cost : nat
	•	laxity : Z

という分離が最も扱いやすいです。

⸻

Step 2: ScheduleLemmas に基本補題を追加

追加先候補
	•	theories/ScheduleLemmas/ScheduleFacts.v
	•	必要なら新規
	•	theories/ScheduleLemmas/RemainingCost.v
	•	theories/ScheduleLemmas/LaxityFacts.v

最初は既存の ScheduleFacts.v に寄せてもよいですが、量が増えるなら分けた方がきれいです。

⸻

追加したい補題一覧

A. remaining_cost の基本補題

Lemma remaining_cost_le_cost :
  forall jobs m sched j t,
    remaining_cost jobs m sched j t <= job_cost (jobs j).

Lemma completed_implies_remaining_cost_zero :
  forall jobs m sched j t,
    completed jobs m sched j t ->
    remaining_cost jobs m sched j t = 0.

Lemma remaining_cost_zero_implies_completed :
  forall jobs m sched j t,
    remaining_cost jobs m sched j t = 0 ->
    completed jobs m sched j t.

Lemma not_completed_implies_remaining_cost_pos :
  forall jobs m sched j t,
    ~ completed jobs m sched j t ->
    remaining_cost jobs m sched j t > 0.

B. 1-step 変化補題

これは LLF に入る前にかなり重要です。

まず CPU 1 個だけを見る補題がよいです。
単一CPUでまず使えれば十分だからです。

Lemma service_job_step_uni :
  forall sched j t,
    service_job 1 sched j (S t)
    = service_job 1 sched j t + if runs_on sched j t 0 then 1 else 0.

これを使って:

Lemma remaining_cost_step_running_uni :
  forall jobs sched j t,
    sched t 0 = Some j ->
    ~ completed jobs 1 sched j t ->
    remaining_cost jobs 1 sched j (S t)
    = remaining_cost jobs 1 sched j t - 1.

Lemma remaining_cost_step_not_running_uni :
  forall jobs sched j t,
    sched t 0 <> Some j ->
    remaining_cost jobs 1 sched j (S t)
    = remaining_cost jobs 1 sched j t.

厳密には後者は「その時刻に j が他 CPU で走らない」前提が multicore だと必要ですが、単一CPU版から先に作るのが安全です。

⸻

C. laxity の基本補題

Lemma laxity_unfold :
  forall jobs m sched j t,
    laxity jobs m sched j t =
      Z.of_nat (job_abs_deadline (jobs j))
      - Z.of_nat t
      - Z.of_nat (remaining_cost jobs m sched j t).

Lemma completed_implies_laxity_deadline_minus_now :
  forall jobs m sched j t,
    completed jobs m sched j t ->
    laxity jobs m sched j t =
      Z.of_nat (job_abs_deadline (jobs j)) - Z.of_nat t.

D. 単一CPUでの 1-step laxity 変化

LLF の直感に直結する補題です。
	•	実行している job は
	•	時刻が 1 進む
	•	remaining_cost が 1 減る
	•	したがって laxity は変わらない
	•	待機中の ready job は
	•	時刻だけ 1 進む
	•	remaining_cost は変わらない
	•	したがって laxity は 1 減る

Lemma laxity_step_running_uni :
  forall jobs sched j t,
    sched t 0 = Some j ->
    ~ completed jobs 1 sched j t ->
    laxity jobs 1 sched j (S t) = laxity jobs 1 sched j t.

Lemma laxity_step_not_running_uni :
  forall jobs sched j t,
    sched t 0 <> Some j ->
    laxity jobs 1 sched j (S t) = laxity jobs 1 sched j t - 1.

この 2 本が入ると、LLF の振る舞いの説明力がかなり上がります。

⸻

Step 3: MetricChooser.v を新設する

新規ファイル
	•	theories/UniPolicies/MetricChooser.v

目的

EDF の min_dl_job は、実質的に
	•	候補 list
	•	比較キー
	•	最小を返す

という一般パターンです。
これを一般化すると EDF と LLF が同じ枠に乗ります。

⸻

追加する定義

1. 最小 metric 選択関数

Fixpoint min_metric_job
    (metric : JobId -> Z) (l : list JobId) : option JobId :=
  match l with
  | [] => None
  | j :: rest =>
    match min_metric_job metric rest with
    | None => Some j
    | Some j' =>
        if Z.leb (metric j) (metric j') then Some j else Some j'
    end
  end.

Nat ではなく Z にしておくと EDF も LLF も同じ形で扱えます。

EDF 側では

Definition edf_metric (jobs : JobId -> Job) (j : JobId) : Z :=
  Z.of_nat (job_abs_deadline (jobs j)).

とすれば済みます。

2. eligible filter 付き chooser

Definition choose_min_metric
    (metric : JobId -> Z)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : option JobId :=
  min_metric_job metric (filter (fun j => eligibleb jobs m sched j t) candidates).


⸻

追加したい補題

EDF で既にあるものをほぼ一般化します。

Lemma min_metric_job_none_iff : ...
Lemma min_metric_job_in : ...
Lemma min_metric_job_min : ...

Lemma choose_min_metric_eligible : ...
Lemma choose_min_metric_none_if_no_eligible : ...
Lemma choose_min_metric_some_if_exists : ...
Lemma choose_min_metric_in_candidates : ...
Lemma choose_min_metric_optimal : ...
Lemma choose_min_metric_unique_min : ...


⸻

既存 EDF への影響

最初は EDF を無理に書き換えなくてもよいです。
ただし最終的には
	•	EDF.v の min_dl_job
	•	choose_edf

を MetricChooser.v ベースに置き換えると重複が減ります。

リファクタリング段階案
	•	第1段階: MetricChooser.v を追加し、LLF だけで利用
	•	第2段階: EDF を MetricChooser ベースへ置換
	•	第3段階: EDF 独自補題を共通補題へ寄せる

最初から EDF を触りすぎない方が安全です。

⸻

Step 4: UniPolicies/Laxity.v を追加

新規ファイル
	•	theories/UniPolicies/Laxity.v

必要なら後で
	•	theories/UniPolicies/LaxityLemmas.v

に分けてもよいです。

⸻

このファイルで定義するもの

1. LLF metric

Definition llf_metric
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) (t : Time)
    (j : JobId) : Z :=
  laxity jobs m sched j t.

2. LLF chooser

Definition choose_llf
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (t : Time) (candidates : list JobId) : option JobId :=
  choose_min_metric (llf_metric jobs m sched t) jobs m sched t candidates.

3. LLF が GenericSchedulingAlgorithm を満たすこと

EDF と同様に

Definition llf_generic_spec : GenericSchedulingAlgorithm := ...

を構成します。

必要な obligation は
	•	chosen → eligible
	•	eligible candidate exists → Some
	•	no eligible candidate → None
	•	chosen ∈ candidates

です。
これは MetricChooser.v の補題でほぼ埋まるはずです。

⸻

policy-specific lemma として入れたいもの

1. 最小 laxity 性

Theorem choose_llf_min_laxity :
  forall jobs m sched t candidates j,
    choose_llf jobs m sched t candidates = Some j ->
    forall j', In j' candidates ->
    eligible jobs m sched j' t ->
    laxity jobs m sched j t <= laxity jobs m sched j' t.

2. 完全候補集合版

Lemma choose_llf_complete : ...
Lemma choose_llf_optimal : ...

3. 0-laxity job の局所性質

最初は強すぎる progress ではなく、局所選択性だけで十分です。

Lemma choose_llf_prefers_zero_laxity :
  forall jobs sched t candidates j,
    choose_llf jobs 1 sched t candidates = Some j ->
    ...

あるいはもっと直接的に、

Lemma choose_llf_zero_laxity_min :
  forall jobs sched t candidates j j',
    choose_llf jobs 1 sched t candidates = Some j ->
    In j' candidates ->
    eligible jobs 1 sched j' t ->
    laxity jobs 1 sched j' t = 0 ->
    laxity jobs 1 sched j t <= 0.

くらいから始めるのが現実的です。

⸻

bundle / scheduler 化

既存の EDF/FIFO/RR と命名を揃えます。

たとえば

Definition llf_policy : SchedulingAlgorithm := ...
Definition llf_policy_sane : SchedulingAlgorithmSpecSanity llf_policy := ...
Definition choose_llf_refines_llf_policy : ...
Definition llf_bundle : UniSchedulerBundle := ...
Definition llf_scheduler : Scheduler := ...

命名は既存 EDF に合わせて調整してください。

⸻

Step 5: PartitionedPolicies/PartitionedLLF.v を追加

新規ファイル
	•	theories/PartitionedPolicies/PartitionedLLF.v

方針

これは EDF/FIFO/RR と同様に、薄い wrapper にします。
partitioned の本体ロジックは既に Partitioned.v / PartitionedCompose.v にあるはずなので、ここでは
	•	per-CPU に LLF bundle を置く
	•	既存 compose を使う

だけにするのがよいです。

⸻

追加内容のイメージ

Definition partitioned_llf_scheduler
    (assign : JobId -> CPU)
    (n : nat)
    ... : Scheduler := ...

必要に応じて

Definition partitioned_llf_spec := ...
Lemma partitioned_llf_valid : ...

も追加します。

⸻

この段階で証明したいこと

最初は「理論の深い性質」ではなく、構成の健全性 で十分です。
	•	per-CPU chooser が valid
	•	compose 後も valid
	•	assignment respect を壊さない
	•	CPU ごとの local LLF が global schedule の各 CPU に投影される

⸻

Step 6: 更新すべき周辺ファイル

1. _CoqProject

新規ファイルを読み込むなら順序を更新します。

追加候補:
	•	theories/UniPolicies/MetricChooser.v
	•	theories/UniPolicies/Laxity.v
	•	theories/PartitionedPolicies/PartitionedLLF.v

2. plan/roadmap.md

実装済み項目として更新
	•	remaining_cost
	•	laxity
	•	metric chooser
	•	LLF
	•	partitioned LLF

3. plan/what_to_prove.md

完了済み・次の未完項目を反映

4. progress/

必要なら
	•	laxity_plan.md
	•	laxity_progress.md

を追加

⸻

具体的なファイル編集計画

変更ファイル
	•	theories/ScheduleModel.v
	•	theories/ScheduleLemmas/ScheduleFacts.v
もしくは新規補題ファイル
	•	_CoqProject

新規ファイル
	•	theories/UniPolicies/MetricChooser.v
	•	theories/UniPolicies/Laxity.v
	•	theories/PartitionedPolicies/PartitionedLLF.v

⸻

実装フェーズをさらに細かく分けた plan

Phase A: 状態量追加

A1

ScheduleModel.v に remaining_cost を追加

A2

ScheduleModel.v に laxity : Z を追加

A3

completed と remaining_cost の対応補題を追加

完了条件:
	•	remaining_cost / laxity が定義されている
	•	unfold 系と zero/completed 系補題が通る

⸻

Phase B: 単一CPU向け変化補題

B1

service_job の 1-step 展開補題

B2

実行時 remaining_cost 減少補題

B3

非実行時 remaining_cost 不変補題

B4

実行時 laxity 不変補題

B5

待機時 laxity 減少補題

完了条件:
	•	LLF の直感を支える基本補題が揃う

⸻

Phase C: generic chooser 化

C1

MetricChooser.v に min_metric_job

C2

choose_min_metric

C3

構造補題
	•	in
	•	none iff empty
	•	minimality

C4

eligible-filter 付き chooser 補題
	•	eligible
	•	some-if-exists
	•	none-if-no-eligible
	•	in-candidates

完了条件:
	•	EDF と LLF の両方に使える chooser 抽象がある

⸻

Phase D: LLF 実装

D1

llf_metric

D2

choose_llf

D3

llf_generic_spec

D4

LLF-specific optimality 補題

D5

bundle / scheduler 化

完了条件:
	•	単一CPU LLF scheduler が既存枠に載る

⸻

Phase E: partitioned LLF

E1

PartitionedPolicies/PartitionedLLF.v

E2

compose

E3

validity / refinement の最小限

完了条件:
	•	per-CPU LLF を用いた partitioned scheduler が構成できる

⸻

この plan で先送りするもの

今回は以下はやらない方がよいです。
	•	global LLF
	•	top-m minimum-laxity chooser
	•	clustered LLF
	•	LLF の強い schedulability theorem
	•	OS operational semantics との接続

理由は、今の段階ではまず
	•	定義の整合性
	•	単一CPU chooser
	•	partitioned への載せ替え

までを成功させるのが先だからです。

⸻

補題の優先順位

最初に証明すべき補題の優先順位は次です。
	1.	completed_implies_remaining_cost_zero
	2.	not_completed_implies_remaining_cost_pos
	3.	laxity_unfold
	4.	remaining_cost_step_running_uni
	5.	remaining_cost_step_not_running_uni
	6.	laxity_step_running_uni
	7.	laxity_step_not_running_uni
	8.	choose_min_metric_*
	9.	choose_llf_min_laxity

この順なら、途中で詰まりにくいです。

⸻

最終的な次タスク

最初の 1 コミットとしては、これが最もよいです。

次の具体タスク

ScheduleModel.v に remaining_cost と laxity を追加し、ScheduleFacts.v に completed/remaining_cost/laxity の基本補題を入れる。

その次のコミットで

MetricChooser.v を追加する。

その次で

Laxity.v に LLF を入れる。
