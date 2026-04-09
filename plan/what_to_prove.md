# what_to_prove.md

# 証明すべきスケジューリング理論の定理（実装反映版）

このファイルは、現在の実装と更新後の `roadmap.md` を踏まえて、
**これから何を証明していくか** を難易度別に整理したものである。

現在の実装はすでに次の段階まで進んでいる。

- 共通基盤 (`Base.v`, `ScheduleModel.v`, `SchedulerInterface.v`)
- dispatch 抽象 (`DispatchInterface.v`, `DispatchLemmas.v`, `DispatchClassicalLemmas.v`)
- single-CPU bridge (`DispatchSchedulerBridge.v`)
- concrete policy としての EDF / FIFO (`UniPolicies/EDF.v`, `UniPolicies/FIFO.v`)
- partitioned scheduling の基礎 (`Partitioned.v`)
- periodic task model の骨格 (`PeriodicTasks.v`)

したがって、次の中心目標は

- **単一CPUの一般補題層の整備**
- **EDF 最適性定理**
- **task-level EDF 理論への接続**

である。

以下では、難易度を Lv.0 から順に上げる。
難易度は「重要度」ではなく、**現在の実装からどれだけ自然に到達できるか** を基準にしている。

---

# 全体の見取り図

更新後のロードマップに沿うと、証明対象は大きく次の順で積み上がる。

1. **共通基盤の整合性**
2. **dispatch / bridge の健全性**
3. **単一CPU concrete policy の局所仕様**
4. **単一CPUの一般補題層**
5. **EDF 最適性定理**
6. **task-level EDF 理論**
7. **partitioned scheduling の持ち上げ定理**
8. **partitioned EDF / multicore schedulability**
9. **global / clustered scheduling**
10. **OS寄り operational semantics と refinement**

重要なのは、**今の実装では EDF 最適性定理がかなり現実的な次の山** になっていることである。
旧版のように、global scheduling や OS 寄り理論を早い段階の主戦場に置く必要はない。

---

# Lv.0: 共通基盤の定義整合性

ここは単一CPUでも partitioned でも共通の最下層である。
実装上は `ScheduleModel.v` の補題群に対応する。

## 0-1. `runs_on` / `cpu_count` / `service_job` の基本補題

証明すべきこと:

- `service_job` は単調増加
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
- `valid_schedule` から deadline miss 以外の局所的異常が起きない

## 0-4. `feasible` / `feasible_on` の基本関係

証明すべきこと:

- `feasible` と `feasible_on` の関係
- subset を狭めたときの単調性
- `feasible_schedule` から `feasible_schedule_on` が導けること

### 難易度

**最も低い。**
すでに一部は `ScheduleModel.v` に入っているので、残りを整理する段階である。

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

これは `GenericDispatchSpec` の核である。

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
このレベルはかなり mechanize 済みであり、今後は再利用が中心になる。

---

# Lv.2: 単一CPU concrete policy の局所仕様

ここは `UniPolicies/EDF.v` と `UniPolicies/FIFO.v` に対応する。
局所選択則が正しいことを示す段階であり、trace 全体の最適性まではまだ入らない。

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

## 2-3. 将来の concrete policy

今後入れるなら次が候補である。

- Round Robin
- prioritized FIFO
- fixed-priority scheduler

ここではまず、

- queue / rotation / tie-break が局所仕様として正しく書けること

を示す。

### 難易度

**低〜中。**
EDF/FIFO はすでにかなり進んでいる。Round Robin 以降は次の拡張対象になる。

---

# Lv.3: 単一CPUの一般補題層

ここが **次に本格的に整備すべき層** である。
`EDFLemmas.v` や `ScheduleTransform.v` に相当する補題群を想定している。

## 3-1. prefix / suffix / 区間 service の補題

証明すべきこと:

- prefix を伸ばすと `service_job` は減らない
- 区間 `[a,b)` の service を prefix 差で表せる
- completion は prefix service と対応する
- deadline 時刻の比較を service の比較へ落とせる

## 3-2. schedule 変換補題

証明すべきこと:

- 2つの時刻の実行を入れ替えても、他の job の service は不変
- swap 後の total service が保存される
- swap 後も `valid_schedule` が保たれる条件
- ある job を前倒ししたとき、その job の completion は悪化しない
- より遅い deadline の job を後ろへ送っても安全である条件

## 3-3. EDF 違反時刻の抽出

証明すべきこと:

- EDF でない schedule があれば、最初の違反時刻を取れる
- その時刻には、選ばれた job よりも deadline の早い eligible job が存在する
- その job は後続時刻のどこかで実行される、または demand 議論へ帰着できる

## 3-4. EDF 形への正規化

証明すべきこと:

- feasible schedule を、先頭から順に EDF 形へ変換できる
- 変換後も feasible 性を保つ
- finite horizon 上で時刻帰納法が回る

### 難易度

**中。**
ここが次の実装上の核心であり、EDF 最適性定理の下準備である。

---

# Lv.4: EDF 最適性定理

ここが **単一CPU scheduling theory の中心定理** である。
ロードマップ上でも、現在の実装から見た次の大きなマイルストーンである。

## 4-1. 単一CPU EDF 最適性

証明すべきこと:

- feasible な単一CPU job 集合なら EDF でも deadline miss を起こさない
- 形式的には `feasible_on J jobs 1 -> schedulable_by_on J edf_scheduler jobs 1` に近い形
- あるいは「feasible schedule が存在すれば EDF 条件を満たす feasible schedule が存在する」でもよい

## 4-2. 系: EDF 失敗なら infeasible

証明すべきこと:

- 単一CPU・preemptive・独立 job 系では、EDF で失敗するならその job 集合は feasible でない

## 4-3. EDF と feasibility の一致

より整った形としては:

- `feasible_on J jobs 1 <-> schedulable_by_on J edf_scheduler jobs 1`

を目指せる。
ただし最初は片方向だけでも十分に価値がある。

### 難易度

**中〜やや高い。**
理論的重要度は非常に高いが、現在の実装からはかなり自然に到達できる。

---

# Lv.5: task-level EDF 理論

ここから `PeriodicTasks.v` と接続し、job-level 理論を task-level に持ち上げる。

## 5-1. periodic task model の基本補題

証明すべきこと:

- `generated_by_periodic_task` から `valid_job_of_task`
- release / absolute deadline / WCET 境界の基本補題
- `periodic_job_model_on` と `feasible_on` の接続

一部はすでに実装済みである。

## 5-2. implicit-deadline periodic tasks と EDF

証明すべきこと:

- implicit deadline tasks の下で、task-level schedulability を job-level EDF 理論へ落とせる
- task set から誘導される job 集合が EDF 最適性定理の仮定を満たす

## 5-3. 利用率定理

古典的には次を狙う。

- 単一CPU
- independent periodic tasks
- implicit deadline

の下で

- `Σ C_i / T_i <= 1 -> EDF schedulable`

## 5-4. demand bound function への入口

さらに進めるなら:

- demand bound function
- processor demand criterion
- constrained / arbitrary deadline への拡張

### 難易度

**やや高い。**
EDF 最適性のあとに進む自然な task-level 理論である。

---

# Lv.6: partitioned scheduling の持ち上げ定理

ここは `Partitioned.v` に直接対応する。
すでに基礎定理はかなり入っているので、残りを整理して theorem layer として明示化する段階である。

## 6-1. assignment respect / local-to-global validity

証明すべきこと:

- `partitioned_schedule_on` から assignment respect が従う
- 各 CPU 上の local view が正しければ global schedule も valid
- `valid_partitioned_schedule` を安定した公開インターフェースとして使う

## 6-2. service 分解

証明すべきこと:

- partitioned では job の service は割当先 CPU 上の service と一致する
- 他 CPU 上の寄与は 0
- `completed` / `missed_deadline` が割当先 CPU の local schedule に還元できる

## 6-3. local feasible から global feasible

証明すべきこと:

- 各 CPU の `local_jobset` 上で feasible なら global でも feasible
- 各 CPU の valid + feasible から global valid + feasible を導ける

### 難易度

**やや高いが、かなり現実的。**
このレベルは、現在の `Partitioned.v` の延長として自然に進められる。

---

# Lv.7: partitioned EDF / multicore schedulability

partitioned scheduling の具体 policy theory に入る段階である。

## 7-1. partitioned EDF

証明すべきこと:

- 各 CPU が EDF を走らせるとき、global schedule は partitioned EDF である
- `partitioned_scheduler` と `edf_scheduler` を組み合わせた concrete theorem

## 7-2. per-CPU EDF から global schedulability

証明すべきこと:

- 各 CPU 上で EDF-schedulable なら、global partitioned schedule も schedulable
- `partitioned_schedulable_by_on_intro` を concrete policy に適用した定理

## 7-3. task assignment との接続

証明すべきこと:

- assignment が与えられたときの schedulability
- bin packing 的問題は algorithmic 側に分けつつ、理論側は assignment fixed で証明する

### 難易度

**高め。**
ただし global EDF よりはるかに現実的で、単一CPU理論を再利用しやすい。

---

# Lv.8: single-CPU policy の拡充

EDF 以外の policy を library として厚くしていく段階である。

## 8-1. Round Robin

証明すべきこと:

- rotation が正しい
- quantum 消費後に末尾へ送られる
- ready に残り続ける job は再び選ばれる

## 8-2. prioritized FIFO / fixed priority

証明すべきこと:

- 高 priority job を優先する
- 同 priority 内では FIFO
- starvation 条件や bounded waiting の議論への入口を作る

## 8-3. 比較定理

証明すべきこと:

- FIFO は EDF のような最適性を持たないことの反例
- RR は fairness では有利だが deadline optimal ではないこと
- policy ごとの強みを theorem/counterexample として整理する

### 難易度

**高め。**
EDF 最適性のあとに進めると、比較の軸が明確になる。

---

# Lv.9: global / clustered scheduling

ここからは現在の実装にはまだ直接入っていない。
将来の multicore 拡張として整理する段階である。

## 9-1. global scheduling の局所仕様

証明すべきこと:

- ready set から高々 `m` 個選ぶ
- 選ばれた job たちは distinct
- CPU ごとの割当が矛盾しない

## 9-2. global EDF

証明すべきこと:

- ready job のうち deadline 最小 `m` 個を選ぶ
- より遅い deadline job を、より早い deadline job より先に置かない

## 9-3. clustered scheduling

証明すべきこと:

- cluster ごとの local scheduler
- cluster 間 migration 制約
- partitioned と global の中間モデルとしての基本補題

## 9-4. multicore work-conserving / one-copy invariant

証明すべきこと:

- runnable job があり、それを走らせられる idle CPU があるなら無駄に idle しない
- 各 job は任意時刻で高々 1 箇所にしか存在しない

### 難易度

**高い。**
今の実装からはまだ一段飛躍がある。

---

# Lv.10: OS寄り operational semantics と refinement

最後に、抽象スケジューリング理論を OS 寄りモデルへ接続する。
この層は現在の job-level / schedule-level 理論のかなり先にある。

## 10-1. per-CPU machine invariants

証明すべきこと:

- `current[c]` と runqueue の排他
- blocked / ready / running / completed / migrating の分割
- one-copy invariant

## 10-2. wakeup / migration / timer / preemption

証明すべきこと:

- migration で job が lost しない
- wakeup が正しい queue / CPU に入る
- timer が正しく reschedule を引き起こす
- preemption で service が二重計上されない

## 10-3. refinement

証明すべきこと:

- concrete machine trace が abstract schedule に対応する
- abstract EDF / FIFO / RR が concrete 実装の上位仕様になる

### 難易度

**最上位クラス。**
これはスケジューリング理論ライブラリの先にある、OS 実装検証の段階である。

---

# 直近の優先順位

現在の実装状況を踏まえると、次の優先順位が自然である。

## 最優先

1. **Lv.3 単一CPUの一般補題層** を整備する
   - `service_job` / `completed` / prefix / swap 補題
   - EDF 違反時刻抽出
   - EDF 形への正規化

2. **Lv.4 EDF 最適性定理** を証明する
   - `EDFOptimality.v` の導入

## 次点

3. **Lv.5 task-level EDF 理論** に進む
   - `PeriodicTasks.v` と接続
   - 利用率定理や dbf への入口

4. **Lv.6 partitioned scheduling の持ち上げ定理** を整理する
   - `valid_partitioned_schedule` を安定した公開述語として育てる

5. **Lv.7 partitioned EDF** に進む
   - per-CPU EDF の multicore への持ち上げ

---

# まとめ

今の開発段階では、重要なのは

- まず単一CPU理論を完成させること
- その中心定理として EDF 最適性を置くこと
- そのあと task-level EDF と partitioned EDF へ進むこと

である。

したがって、難易度表も

- **共通基盤**
- **dispatch / single-CPU bridge**
- **single-CPU policy**
- **EDF 最適性**
- **task-level EDF**
- **partitioned EDF**
- **global / OS寄り理論**

の順に並べるのが、現在の実装と最も整合的である。
