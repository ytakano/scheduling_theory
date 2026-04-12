# New Roadmap

## 0. 現在地

このプロジェクトは、単なる schedulability analysis ライブラリではなく、  
**executable scheduler semantics** と  
**scheduling-algorithm refinement**  
を中心に据えた Rocq formalization を目指している。

最新実装では、すでに次が揃っている。

- 共通 schedule / service / feasibility / scheduler interface
- generic scheduling-algorithm abstraction
- canonical bridge / normalization skeleton / optimality skeleton
- 単一CPU policy:
  - FIFO
  - Round Robin
  - EDF
  - LLF
- EDF optimality
- LLF optimality の骨格と repair / normalization / optimality
- partitioned scheduling の基本構成
- partitioned EDF / FIFO / RR / LLF の policy wrapper
- periodic task の初期層

したがって今後の主眼は、
**単一CPU policy を増やすことそのもの**ではなく、
**共通理論の安定化 → multicore 理論 → OS semantics → refinement の強化**
に置く。

---

## 1. 設計の主軸

### 1.1 何を中心に据えるか

本プロジェクトの中心は次の 4 点である。

1. executable scheduler semantics
2. concrete scheduling algorithm
3. abstract policy / validity / refinement の分離
4. uniprocessor から multicore / OS semantics への拡張

### 1.2 何を後段に置くか

以下は重要だが、中心構造ではなく後段に置く。

- schedulability analysis
- response-time analysis
- utilization-based tests
- task model ごとの classical theorem library

つまり、**解析のための理論**ではなく、  
**意味論・アルゴリズム・refinement のための理論**を先に固める。

---

## 2. Phase A: 単一CPU共通理論の固定

この phase の目標は、
EDF/LLF のために作った仕組みを「個別定理の集合」ではなく、
**再利用可能な単一CPU scheduling theory core** として整理し直すことにある。

### A-1. generic canonicalization 層の安定化

対象:

- `SchedulingAlgorithmCanonicalBridge`
- `SchedulingAlgorithmNormalization`
- `SchedulingAlgorithmOptimalitySkeleton`
- `Design.md`

やること:

- generic canonical bridge / normalization skeleton / finite optimality skeleton
  を、単一CPU policy 拡張の標準インターフェースとして固定する
- policy 固有に残る責務を
  - local canonicality
  - local repair
  - prefix agreement
  に分けて明示する
- `Design.md` とコードコメントを同期させ、
  新 policy 追加者が読むべき設計文書を維持する

完了条件:

- 「新しい単一CPU policy を 1 つ追加して finite optimality pipeline に接続する」
  ための最小テンプレートが明確
- EDF / LLF の両方がそのテンプレートの実例になっている
- 残作業が「設計探索」ではなく
  「新 policy への適用」「コメント保守」「追加補題の整備」として整理されている

Current status:

- The generic canonicalization core already exists.
- EDF and LLF both instantiate that core successfully.
- The remaining work is not to invent a new abstraction, but to stabilize the
  boundary between generic and policy-specific obligations.
- In particular, `CanonicalRepairSpec` and `ChooseAgreesBefore` should become
  the documented template for adding future uniprocessor policies.

### A-2. metric-based chooser 理論の整理

対象:

- `MetricChooser.v`
- `MetricChooserLemmas.v`
- EDF / LLF chooser 関連補題

やること:

- static metric と dynamic metric を明確に整理する
- `deadline`
- `priority`
- `laxity`
の違いをインターフェース上で明確化する
- prefix-invariance が必要な箇所を共通補題に寄せる

完了条件:

- EDF と LLF を「metric-based policy の 2 例」として説明できる
- 今後 LST や別の dynamic metric policy を追加しやすい

Current status:

- Much of the practical groundwork is already present through EDF and LLF.
- The remaining task is mainly conceptual cleanup and interface-level
  documentation, rather than a missing implementation core.

### A-3. 単一CPUの定理一覧を整理する

対象:

- `what_to_prove.md`
- 単一CPU policy ファイル群

やること:

- すでに証明済みのもの
- skeleton はあるが整理不足のもの
- 未着手のもの
を分離する
- 「定義」「局所性質」「repair」「normalization」「optimality」の 5 層で整理する
- `Design.md` の architecture 用語と `what_to_prove.md` の inventory 用語を揃える

完了条件:

- 単一CPUについて何が終わっていて、何が未完かが一目で分かる

---

## 3. Phase B: partitioned multicore を理論として完成させる

現状、partitioned scheduling は「multicore への最初の橋」として最も自然であり、
Design Principles の方針とも整合的である。
したがって次の主戦場は partitioned である。

### B-1. partitioned compose の定理層を完成させる

対象:

- `Partitioned.v`
- `PartitionedCompose.v`

やること:

- per-CPU valid から global valid
- service decomposition
- completion / missed deadline の持ち上げ
- feasible / schedulable の持ち上げ
を補題として揃える

完了条件:

- 各 CPU 上の uniprocessor reasoning を global partitioned schedule に持ち上げる標準補題群がある

Current status:

- The basic partitioned construction and policy wrappers already exist.
- The remaining work is to turn the current construction into a stable theorem
  layer for lifting uniprocessor reasoning to the partitioned multicore level.

### B-2. partitioned policy lifting を共通化する

対象:

- `PartitionedPolicies/PartitionedEDF.v`
- `PartitionedPolicies/PartitionedFIFO.v`
- `PartitionedPolicies/PartitionedLLF.v`
- `PartitionedPolicies/PartitionedRR.v`

やること:

- policy ごとの wrapper を共通パターンに揃える
- 「assignment respect + per-CPU scheduler validity + global schedule validity」を分離して整理する
- 単一CPU optimality / scheduler_rel / schedulable_by の lifting 方針を固定する

完了条件:

- partitioned policy 追加時に必要な構成要素が統一される
- EDF / LLF / FIFO / RR の partitioned 版が同じ形式で並ぶ

### B-3. partitioned schedulability lifting を定理化する

やること:

- 各 CPU ごとに schedulable なら、assignment 下で partitioned global scheduler も schedulable
- feasible / schedulable の lifting を theorem として固定する

完了条件:

- 「単一CPUの結果を multicore partitioned へ持ち上げる」標準 theorem がある

---

## 4. Phase C: multicore 共通意味論の導入

partitioned の次に進むべきは、
いきなり global EDF の解析ではなく、
**multicore 共通意味論** の整備である。

### C-1. multicore 共通 validity / exclusivity / one-copy invariant

やること:

- 同時に複数 CPU で同一 job を走らせない
- CPU ごとの slot 妥当性
- affinity / allowed CPU の制約
- multicore service の一貫性
を整理する

完了条件:

- partitioned / global / clustered で共通に使える multicore validity 層ができる

### C-2. multicore scheduler abstraction

やること:

- single-CPU chooser ではなく
  - top-m selection
  - per-CPU local chooser
  - queue-based semantics
などを表せる抽象化を作る
- partitioned / global / clustered を同じ大枠に載せる

完了条件:

- multicore scheduling algorithm interface の原型が定まる

### C-3. multicore dynamic-metric policy の足場

やること:

- EDF / LLF の multicore 版で必要になる
  - candidate completeness
  - top-m metric choice
  - migration を伴う選択
の共通補題を準備する

完了条件:

- global EDF / global LLF を定義する前提が揃う

---

## 5. Phase D: global / clustered scheduling

この phase ではじめて、partitioned を超えて本格的な multicore scheduling policy に進む。

### D-1. global scheduling の最小骨格

やること:

- global ready set から m 個選ぶ semantics
- no-duplication
- top-m metric 選択
- idle core の扱い
を定義する

最初の対象:

- global EDF

理由:

- 既存の EDF 理論を最も活かしやすい
- priority ordering が明確
- global scheduling の共通問題を最初に露出できる

### D-2. clustered scheduling

やること:

- CPU cluster ごとの local-global hybrid モデル
- cluster 内 chooser と cluster 間 isolation
- partitioned と global の中間として整理する

完了条件:

- partitioned / clustered / global が 3 系統として並ぶ

### D-3. global LLF は後続で導入

理由:

- LLF は state-dependent metric のため multicore で難易度が高い
- まず global EDF を通して multicore top-m semantics を安定化すべき

---

## 6. Phase E: OS-level operational semantics

Design Principles に最も強く対応する長期フェーズ。
ここでは schedule を「結果」ではなく、「状態遷移の観測像」として捉える。

### E-1. operational state の導入

候補:

- per-CPU current
- local/global runqueue
- wakeup
- block
- completion
- timer event
- preemption point
- migration event
- IPI / reschedule request

### E-2. trace semantics と schedule projection

やること:

- operational trace から schedule を射影する
- schedule-level theorem を trace-level invariant へ接続する
- service / completion / missed deadline と trace semantics の整合性を示す

### E-3. executable scheduler state machine

やること:

- 単なる chooser 関数ではなく、queue を持つ実行可能 state machine を formalize する
- RR や FIFO の operational semantics を先に行う
- EDF / LLF はその次に接続する

完了条件:

- 「抽象 schedule semantics」と「OSに近い operational semantics」が refinement で結ばれる

---

## 7. Phase F: refinement の強化

この phase は本プロジェクトの中核であり、OS semantics 導入後に本格化する。

### F-1. abstract policy -> executable algorithm

すでに単一CPU EDF / LLF で実施している流れを一般化する。

- abstract policy
- chooser / choose
- canonical schedule
- normalization
- scheduler relation
- schedulable_by

を refinement pipeline として整理する。

### F-2. executable algorithm -> operational scheduler

やること:

- queue state を持つ operational scheduler が、
  schedule-level chooser semantics を refine することを示す
- runqueue / migration / wakeup のある実装寄りモデルを、
  既存 schedule semantics に結びつける

### F-3. operational scheduler -> OS kernel model

長期目標:

- timer / IPI / wakeup race を含む OS scheduling semantics
- 実行可能 kernel scheduling model
- schedule-level theorem との接続

---

## 8. Phase G: task model extensions

task model は semantic core の上に載る extension として扱う。

### G-1. periodic tasks

やること:

- task-to-job generation
- hyperperiod reasoning
- release pattern の基本補題
- schedule semantics との接続

### G-2. sporadic tasks

periodic より一般化した release 制約を導入する

### G-3. DAG tasks

これは job generation ではなく内部構造拡張として扱う

- node-level ready
- precedence
- carry-in / carry-out 的構造
- scheduler semantics への接続

---

## 9. Phase H: analysis を上に載せる

analysis は core の上に構築する。

### H-1. partitioned response-time / schedulability
### H-2. global EDF analysis
### H-3. multicore interference / busy interval
### H-4. LLF / dynamic-metric analysis
### H-5. speedup bound / policy comparison

ただし、これは multicore semantics と refinement が十分安定してからでよい。

---

## 10. 現実的な優先順序

### Step 1
単一CPU共通理論の固定

- canonicalization / normalization / optimality skeleton の保守運用化
- `Design.md` / `roadmap.md` / `what_to_prove.md` の同期
- metric-based chooser の整理
- what_to_prove の再構成

### Step 2
partitioned multicore の定理層を完成

- compose 補題
- schedulability lifting
- policy lifting の共通化

### Step 3
multicore 共通意味論

- no-duplication
- affinity
- multicore validity
- top-m chooser の抽象化

### Step 4
global EDF

### Step 5
clustered scheduling

### Step 6
OS-level operational semantics

### Step 7
refinement を operational model まで延長

### Step 8
periodic / sporadic / DAG extensions

### Step 9
response-time / schedulability / speedup bound

---

## 11. 次に着手すべき具体タスク

現状から最も自然な次タスクは以下。

### 優先度A
`PartitionedCompose.v` と `Partitioned.v` を中心に、
**per-CPU reasoning を global reasoning に持ち上げる定理群**を完成させる。

### 優先度B
partitioned EDF / FIFO / RR / LLF の wrapper を見比べて、
**policy lifting の共通パターン**を抽出する。

### 優先度C
`what_to_prove.md` を、
「generic normalization / finite optimality pipeline がすでに存在する」前提で更新し、
未完部分を局所 policy obligation と multicore 側課題に切り分ける。

---

## 12. このロードマップの要点

- 旧 roadmap の「単一CPU基盤構築」はかなり完了している
- いま重要なのは、単一CPUの成果を**理論的に固定して再利用可能化**し、
  policy 追加テンプレートとして維持すること
- 次の本命は **partitioned multicore**
- その次に **multicore 共通意味論**
- さらにその先に **global/clustered** と **OS operational semantics**
- analysis は最後に上に積む
