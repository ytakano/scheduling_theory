# What to Prove

# 証明すべきスケジューリング理論の定理（scheduler semantics / refinement 中心版）

このファイルは、現在の実装と更新後の `roadmap.md` を踏まえて、
**これから何を証明していくか** を難易度別に整理したものである。

この版では、証明対象の重心を

- **解析結果を増やすこと**
ではなく、
- **実行可能な scheduler semantics の整備**
- **abstract policy と concrete dispatcher の refinement**
- **single-CPU から multicore / OS semantics への拡張**

に置いている。

現在の実装はすでに次の段階まで進んでいる。

- 共通基盤 (`Base.v`, `ScheduleModel.v`, `SchedulerInterface.v`)
- dispatch 抽象 (`DispatchInterface.v`, `DispatchLemmas.v`, `DispatchClassicalLemmas.v`)
- single-CPU bridge (`DispatchSchedulerBridge.v`)
- concrete policy としての EDF / FIFO (`UniPolicies/EDF.v`, `UniPolicies/FIFO.v`)
- partitioned scheduling の基礎 (`Partitioned.v`)
- periodic task model の骨格 (`PeriodicTasks.v`)

したがって、次の中心目標は

- **single-CPU scheduler semantics の整理**
- **dispatcher refinement の導入**
- **EDF 最適性定理**
- **partitioned / global / OS semantics への接続**

である。

以下では、難易度を Lv.0 から順に上げる。
難易度は「重要度」ではなく、**現在の実装からどれだけ自然に到達できるか** を基準にしている。

---

# 全体の見取り図

更新後のロードマップに沿うと、証明対象は大きく次の順で積み上がる。

1. **共通基盤の整合性**
2. **dispatch / bridge の健全性**
3. **policy / scheduler validity / concrete dispatcher の局所仕様**
4. **dispatcher refinement**
5. **single-CPU の一般補題層**
6. **EDF 最適性定理**
7. **single-CPU policy family の拡充**
8. **partitioned multicore semantics**
9. **global / clustered multicore semantics**
10. **affinity / migration semantics**
11. **OS寄り operational semantics と refinement**
12. **task model / analysis adapter**

重要なのは、**今後の中心が「解析結果」そのものではなく、「scheduler semantics と refinement」になること**である。
EDF 最適性は依然として重要な中核定理だが、それは **dispatcher refinement を持つ単一CPU理論の代表例**として位置付けられる。

---

# Lv.0: 共通基盤の定義整合性

ここは単一CPUでも multicore でも共通の最下層である。
実装上は `ScheduleModel.v` を中心とする補題群に対応する。

## 0-1. `runs_on` / `cpu_count` / `service_job` の基本補題

証明すべきこと:

- `service_job` は時間に関して単調増加
- 1 tick あたりの増分は `cpu_count` に一致する
- `sequential_jobs` 仮定の下で、1 tick で高々 1 増える
- 実行されなければ増えない
- 単一CPUでは `service_job 1` がそのまま実行回数になる

## 0-2. `completed` / `eligible` / `ready` / `running` の整合性

証明すべきこと:

- `completed` なら `eligible` でない
- release 前には `eligible` でない
- `ready -> eligible`
- `running -> eligible`
- `ready` と `running` は両立しない
- `completed` は時間に関して単調

## 0-3. `valid_schedule` の基本性質

証明すべきこと:

- release 前に走らない
- completed 後に走らない
- スケジュールされた job は常に eligible
- `valid_schedule` から局所的な異常が起きない

## 0-4. `feasible` / `feasible_on` の基本関係

証明すべきこと:

- `feasible` と `feasible_on` の関係
- subset を狭めたときの単調性
- `feasible_schedule` から `feasible_schedule_on` が導けること

### 難易度

**最も低い。**
現在の実装を今後の理論全体で再利用するための整理段階である。

---

# Lv.1: dispatch 抽象と bridge の健全性

ここは現在の実装でかなり進んでいる層であり、
`DispatchInterface.v` と `DispatchSchedulerBridge.v` に対応する。

## 1-1. Generic dispatch の局所健全性

証明すべきこと:

- dispatch が返した job は eligible
- eligible な candidate があれば `Some` を返す
- eligible candidate がなければ `None`
- 選ばれた job は candidate list に属する

## 1-2. Candidate source の健全性

証明すべきこと:

- candidate source が返す job は対象 job 集合 `J` に属する
- `J` の eligible job は candidate list に含まれる
- subset reasoning が concrete policy に漏れない

## 1-3. single-CPU bridge の妥当性

証明すべきこと:

- `single_cpu_dispatch_schedule` が valid schedule を作る
- CPU 0 以外は常に idle
- 実際に動く job は subset `J` に属する
- subset 上の feasible 性から `schedulable_by_on` を導ける

### 難易度

**低い。**
このレベルはかなり mechanize 済みであり、今後は公開インターフェースとして安定化する段階である。

---

# Lv.2: policy / scheduler validity / concrete dispatcher の局所仕様

ここでは、単一CPU上で

- abstract policy
- schedule がその policy を満たすこと
- concrete dispatcher の局所仕様

を分けて整理する。

## 2-1. EDF の局所補題

証明すべきこと:

- `choose_edf` が選ぶ job は eligible
- eligible candidate が存在すれば `choose_edf` は `Some` を返す
- `choose_edf` は candidate の中から選ぶ
- `choose_edf` が選んだ job は、他の eligible candidate より deadline が遅くない
- 一意な最小 deadline があるとき、その job を選ぶ

## 2-2. FIFO の局所補題

証明すべきこと:

- `choose_fifo` は最初の eligible job を選ぶ
- 前に eligible な job があれば、それを飛ばさない
- candidate list がそのまま FIFO 順序を表すこと

## 2-3. policy validity の局所述語

証明すべきこと:

- `respects_policy_at` のような局所述語が妥当であること
- schedule validity と policy validity が混同されていないこと
- tie を含む仕様を policy 側で吸収できること

## 2-4. 将来の concrete policy

今後入れる候補:

- Round Robin
- prioritized FIFO
- fixed-priority scheduler

ここではまず、

- queue / rotation / tie-break が局所仕様として正しく書けること

を示す。

### 難易度

**低〜中。**
EDF/FIFO はすでにかなり進んでいる。ここでは「chooser の正しさ」だけでなく、「policy / validity / chooser の分離」を進める。

---

# Lv.3: dispatcher refinement

ここは更新後のロードマップで新しく前面に出した層である。

## 3-1. dispatcher が policy を実装すること

証明すべきこと:

- `choose_edf` が EDF policy を実装する
- `choose_fifo` が FIFO policy を実装する
- tie を含む場合でも、concrete dispatcher が abstract policy の許容範囲に入る

## 3-2. dispatcher が scheduler validity を生むこと

証明すべきこと:

- `single_cpu_dispatch_schedule` が対応する policy validity を満たす
- bridge を通した concrete schedule が abstract scheduler semantics に入る
- dispatcher の出力は valid schedule と policy validity の両方を満たす

## 3-3. deterministic / executable 性

証明すべきこと:

- concrete dispatcher が決定的であること
- finite candidate ベースで chooser が構成的に定義されていること
- `None` を返す条件が abstract 側の idle 条件と一致すること

### 難易度

**中。**
ここは単なる dispatch 抽象から一歩進み、**理論と実装の接続**を定理として明示化する段階である。

---

# Lv.4: single-CPU の一般補題層

ここが **次に本格的に整備すべき層** である。
`EDFLemmas.v` や `ScheduleTransform.v` に相当する補題群を想定している。

## 4-1. prefix / suffix / 区間 service の補題

証明すべきこと:

- prefix を伸ばすと `service_job` は減らない
- 区間 `[a,b)` の service を prefix 差で表せる
- completion は prefix service と対応する
- deadline 時刻の比較を service の比較へ落とせる

## 4-2. schedule 変換補題

証明すべきこと:

- 2つの時刻の実行を入れ替えても、他の job の service は不変
- swap 後の total service が保存される
- swap 後も `valid_schedule` が保たれる条件
- ある job を前倒ししたとき、その job の completion は悪化しない
- より遅い deadline の job を後ろへ送っても安全である条件

## 4-3. EDF 違反時刻の抽出

証明すべきこと:

- EDF でない schedule があれば、最初の違反時刻を取れる
- その時刻には、選ばれた job よりも deadline の早い eligible job が存在する
- その job は finite candidate の中から取り出せる
- 必要なら Classical を使わずに議論できる

## 4-4. EDF 形への正規化

証明すべきこと:

- feasible schedule を、先頭から順に EDF 形へ変換できる
- 変換後も feasible 性を保つ
- finite horizon 上で時刻帰納法が回る

### 難易度

**中。**
ここが EDF 最適性定理と dispatcher refinement の両方を支える核心である。

---

# Lv.5: EDF 最適性定理

ここが **単一CPU scheduling theory の中心定理** である。
ただしこの版では、EDF 最適性は **dispatcher refinement を伴う代表定理** として位置付ける。

## 5-1. 単一CPU EDF 最適性

証明すべきこと:

- feasible な単一CPU job 集合なら EDF でも deadline miss を起こさない
- 形式的には `feasible_on J jobs 1 -> schedulable_by_on J edf_scheduler jobs 1` に近い形
- あるいは「feasible schedule が存在すれば EDF 条件を満たす feasible schedule が存在する」でもよい

## 5-2. 系: EDF 失敗なら infeasible

証明すべきこと:

- 単一CPU・preemptive・独立 job 系では、EDF で失敗するならその job 集合は feasible でない

## 5-3. EDF と feasibility の一致

より整った形としては:

- `feasible_on J jobs 1 <-> schedulable_by_on J edf_scheduler jobs 1`

を目指せる。
ただし最初は片方向だけでも十分に価値がある。

## 5-4. refinement つき EDF 定理

証明すべきこと:

- `choose_edf` が生成する schedule は EDF validity を満たす
- feasible なら abstract EDF schedule だけでなく、concrete EDF dispatcher による schedule でも feasible
- abstract optimality と concrete implementation が接続される

### 難易度

**中〜やや高い。**
理論的重要度は非常に高く、現在の実装からもかなり自然に到達できる。

---

# Lv.6: single-CPU policy family の拡充

EDF 以外の policy を同じ枠組みで扱い、理論化を広げる段階である。

## 6-1. Round Robin

証明すべきこと:

- rotation が正しい
- quantum 消費後に末尾へ送られる
- ready に残り続ける job は再び選ばれる
- RR dispatcher が RR policy を実装する

## 6-2. prioritized FIFO / fixed priority

証明すべきこと:

- 高 priority job を優先する
- 同 priority 内では FIFO
- concrete chooser が対応する policy class を実装する

## 6-3. 比較定理

証明すべきこと:

- FIFO は EDF のような最適性を持たないことの反例
- RR は fairness では有利だが deadline optimal ではないこと
- policy ごとの強みを theorem / counterexample として整理する

### 難易度

**高め。**
EDF のあとに進めることで、比較の軸が明確になる。

---

# Lv.7: partitioned multicore semantics

ここは `Partitioned.v` に直接対応する。
ここから multicore を **解析対象** ではなく **意味論対象** として本格的に扱う。

## 7-1. assignment respect / local-to-global validity

証明すべきこと:

- `partitioned_schedule_on` から assignment respect が従う
- 各 CPU 上の local view が正しければ global schedule も valid
- `valid_partitioned_schedule` を安定した公開インターフェースとして使う

## 7-2. service 分解

証明すべきこと:

- partitioned では job の service は割当先 CPU 上の service と一致する
- 他 CPU 上の寄与は 0
- `completed` / `missed_deadline` が割当先 CPU の local schedule に還元できる

## 7-3. local refinement から global refinement

証明すべきこと:

- 各 CPU の local dispatcher refinement から global partitioned refinement を導ける
- local EDF / FIFO / RR が global partitioned semantics に持ち上がる
- partitioned scheduler が abstract partitioned policy を実装する

### 難易度

**やや高いが、かなり現実的。**
現在の `Partitioned.v` を theorem layer として育てる段階である。

---

# Lv.8: global / clustered multicore semantics

ここからは現在の実装にはまだ直接入っていない。
将来の multicore 拡張として整理する段階である。

## 8-1. global scheduling の局所仕様

証明すべきこと:

- ready set から高々 `m` 個選ぶ
- 選ばれた job たちは distinct
- CPU ごとの割当が矛盾しない

## 8-2. global EDF

証明すべきこと:

- ready job のうち deadline 最小 `m` 個を選ぶ
- より遅い deadline job を、より早い deadline job より先に置かない
- top-`m` chooser が global EDF policy を実装する

## 8-3. clustered scheduling

証明すべきこと:

- cluster ごとの local scheduler
- cluster 間 migration 制約
- partitioned と global の中間モデルとしての基本補題
- cluster-local refinement と cluster-global validity の関係

## 8-4. multicore work-conserving / one-copy invariant

証明すべきこと:

- runnable job があり、それを走らせられる idle CPU があるなら無駄に idle しない
- 各 job は任意時刻で高々 1 箇所にしか存在しない

### 難易度

**高い。**
単一CPUとは違って、「1つ選ぶ」ではなく「上位 `m` 個を整合的に選ぶ」必要がある。

---

# Lv.9: affinity / migration semantics

ここは multicore semantics をさらに現実的にする層である。

## 9-1. affinity 制約

証明すべきこと:

- 許可された CPU 上でしか job が実行されない
- affinity 制約と partitioned / clustered / global scheduler の関係が整理できる

## 9-2. migration

証明すべきこと:

- migration で job が lost しない
- migration の前後で one-copy invariant が保たれる
- migration を許す / 禁じる policy の違いを定式化できる

## 9-3. assignment-preserving / migration-aware refinement

証明すべきこと:

- concrete multicore dispatcher が affinity / migration 制約を満たす
- assignment-preserving な scheduler refinement を定義できる

### 難易度

**高い。**
OS 寄りモデルへ進む前の重要な橋渡しになる。

---

# Lv.10: OS寄り operational semantics と refinement

最後に、抽象 scheduling theory を OS 寄りモデルへ接続する。
この層は現在の job-level / schedule-level 理論のかなり先にあるが、本プロジェクトの独自性が最も強く出る。

## 10-1. per-CPU machine invariants

証明すべきこと:

- `current[c]` と runqueue の排他
- blocked / ready / running / completed / migrating の分割
- one-copy invariant

## 10-2. wakeup / migration / timer / preemption

証明すべきこと:

- wakeup が正しい queue / CPU に入る
- timer が正しく reschedule を引き起こす
- preemption で service が二重計上されない
- migration event が局所状態と大域状態の整合性を壊さない

## 10-3. operational step から abstract schedule への対応

証明すべきこと:

- concrete machine trace が abstract schedule に対応する
- operational semantics から schedule semantics を抽出できる
- abstract EDF / FIFO / RR が concrete 実装の上位仕様になる

## 10-4. kernel scheduler refinement

証明すべきこと:

- concrete runqueue 操作が abstract dispatcher と対応する
- concrete scheduler implementation が abstract scheduler spec を満たす

### 難易度

**最上位クラス。**
これは単なる scheduling theory を超え、OS 実装検証へ接続する段階である。

---

# Lv.11: task model / analysis adapter

この層では periodic / sporadic task model や analysis を **本体** ではなく **adapter** として接続する。

## 11-1. periodic task model の基本補題

証明すべきこと:

- `generated_by_periodic_task` から `valid_job_of_task`
- release / absolute deadline / WCET 境界の基本補題
- `periodic_job_model_on` と `feasible_on` の接続

## 11-2. task model と scheduler semantics の橋渡し

証明すべきこと:

- task set から誘導される job 集合が scheduler semantics の仮定を満たす
- implicit deadline tasks の下で task-level schedulability を job-level EDF 理論へ落とせる

## 11-3. analysis adapter

必要なら将来的に次を扱う:

- utilization 定理
- demand bound function
- processor demand criterion
- constrained / arbitrary deadline への拡張

ただしこの層の主目的は、
**analysis 結果そのものを増やすことではなく、scheduler semantics の上に task model / analysis を接続できること**
である。

### 難易度

**やや高い。**
理論としては重要だが、本プロジェクトでは本体より後段に置かれる。

---

# 直近の優先順位

現在の実装状況を踏まえると、次の優先順位が自然である。

## 最優先

1. **Lv.3 dispatcher refinement** を導入する
   - `choose_edf` / `choose_fifo` が policy を実装することを明示する
   - `single_cpu_dispatch_schedule` が scheduler validity を満たすことを整理する

2. **Lv.4 single-CPU の一般補題層** を整備する
   - `service_job` / `completed` / prefix / swap 補題
   - EDF 違反時刻抽出
   - EDF 形への正規化

3. **Lv.5 EDF 最適性定理** を証明する
   - `EDFOptimality.v` の導入
   - abstract optimality と concrete EDF dispatcher の接続

## 次点

4. **Lv.6 single-CPU policy family の拡充**
   - `RoundRobin.v`
   - `PrioritizedFIFO.v`

5. **Lv.7 partitioned multicore semantics**
   - `valid_partitioned_schedule` を安定した公開述語として育てる
   - local refinement から global refinement を導く

6. **Lv.8 global / clustered multicore semantics**
   - top-`m` dispatch の最小骨格
   - global EDF の局所仕様

## さらにその次

7. **Lv.9 affinity / migration semantics**
8. **Lv.10 OS寄り operational semantics と refinement**
9. **Lv.11 task model / analysis adapter**

---

# まとめ

今の開発段階では、重要なのは

- まず **single-CPU scheduler semantics** を整理すること
- **dispatcher refinement** を明示的な theorem layer にすること
- その中心定理として **EDF 最適性** を置くこと
- その後 **multicore semantics** と **OS寄り operational model** へ進むこと

である。

したがって、難易度表も

- **共通基盤**
- **dispatch / bridge**
- **policy / validity / concrete dispatcher**
- **dispatcher refinement**
- **EDF 最適性**
- **single-CPU policy family**
- **partitioned / global / clustered**
- **affinity / migration**
- **OS寄り refinement**
- **task model / analysis adapter**

の順に並べるのが、更新後のロードマップと最も整合的である。