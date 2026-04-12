# what_to_prove.md 追記・修正版

# スケジューリング理論の定理

まず現在地を明確にしておく。

単一CPUについては、すでに

* generic scheduling-algorithm abstraction
* canonicality を scheduling algorithm agreement として捉える generic bridge
* local repair を反復する generic normalization skeleton
* finite witness を `scheduler_rel` に接続する finite optimality skeleton

が存在する。

したがって単一CPUで今後整理すべき対象は、
generic 骨格そのものを新たに作ることではなく、

* 各 policy の局所仕様
* local repair obligation
* prefix agreement obligation
* skeleton の追加 instantiation

を見通しよく並べることにある。

単一CPUのときより難しくなる理由は主に次の4つです。

* 同じ時刻に **複数CPU** が動く
* **同じ job を複数CPUで同時実行してはいけない**
* **partitioned / global / clustered** で理論が分かれる
* OS 寄りに行くと **migration / wakeup / IPI / per-CPU runqueue** が入る

なので、難易度表も次の3系統に分けて考えるのがよいです。

* **共通基盤**
* **単一CPU / partitioned**
* **global / OS寄りマルチコア**

以下では、難易度を Lv.0 から順に上げます。

---

# Lv.0: 共通基盤の定義整合性

## 0-1. service の基本補題

証明すべきこと:

* `service` は単調増加
* 1ステップで高々 1 増える
* 実行されたときだけ増える
* 実行されなければ増えない

## 0-2. completed / ready の整合性

証明すべきこと:

* completed なら ready でない
* release 前には ready でない
* completed は単調
* ready は service/completion と整合する

## 0-3. remaining cost / laxity の基本補題

証明すべきこと:

* `remaining_cost` は 0 以上
* completed なら `remaining_cost = 0`
* 実行で `remaining_cost` が減少する
* idle なら `remaining_cost` は変わらない
* `laxity = deadline - now - remaining_cost` の整合性
* 実行で laxity がどう変化するか
* 待機で laxity がどう減るか

### 難易度

**低い**です。
ただし laxity を `nat` で持つか `Z` で持つかで補題の形がかなり変わります。

---

# Lv.1: マルチコア schedule の基本健全性

## 1-1. no-duplication

証明すべきこと:

* 同じ時刻に同じ job が複数CPUで走らない

## 1-2. per-CPU exclusivity

証明すべきこと:

* 各 CPU は各時刻に高々 1 job しか走らせない

## 1-3. affinity / allowed CPU

入れるなら:

* job は許された CPU 上でしか走らない

## 1-4. multicore service の安全性

証明すべきこと:

* migration があっても service は正しく累積される
* CPU 間の移動があっても completion 判定は壊れない

## 1-5. multicore laxity の安全性

証明すべきこと:

* migration があっても `remaining_cost` / `laxity` は job ごとに一意に定まる
* no-duplication のもとで laxity 更新が曖昧にならない

### 難易度

**低〜中**です。

---

# Lv.2: 抽象 scheduler の健全性

## 2-1. choose 健全性

証明すべきこと:

* choose された job は ready
* completed / unreleased job は選ばれない
* allowed CPU でのみ選ばれる

## 2-2. state invariant 保存

証明すべきこと:

* arrival 後も well-formed
* completion 後も well-formed
* requeue / migration 後も well-formed

## 2-3. no-loss

証明すべきこと:

* ready job が勝手に失われない
* migration で job が消えない
* per-CPU queue 間の転送で one-copy が保たれる

## 2-4. metric-min chooser の一般補題

証明すべきこと:

* metric 最小の ready job が選ばれる
* tie-break を含めて決定的
* candidate 集合外の job は選ばれない

ここで EDF は `metric = absolute deadline`、
laxity-based は `metric = laxity` として扱う。

### 難易度

**低〜中**です。

---

# Lv.3: 単一CPU policy の局所仕様

このレベルは policy ごとの chooser / local priority 性質を扱う。
generic normalization や finite optimality はここではなく、
後述の Lv.4-Lv.5 で共通骨格として扱う。

## 3-1. FIFO

* queue 先頭が選ばれる
* overtaking がない
* non-preemptive なら current は完了まで継続

## 3-2. RR

* queue rotation が正しい
* 未完了なら末尾へ戻る
* 巡回順が保存される

## 3-3. Prioritized FIFO

* 高 priority が先
* 同 priority 内 FIFO

## 3-4. EDF

* deadline 最小の ready job を選ぶ
* tie-break 一貫性

For EDF, it is also useful to track the canonicalization pipeline explicitly:

* a canonical-at predicate tied to scheduling algorithm agreement
* a constructive decider for canonicality
* a one-step local repair lemma
* a finite-horizon normalization theorem
* a finite optimality theorem obtained from the shared skeleton

## 3-5. LLF / LST

* laxity 最小の ready job を選ぶ
* tie-break 一貫性
* 0-laxity job があるときの選択性質
* 実行状態に依存する key を使っても chooser が健全

For LLF/LST, the same layered structure is important, but slightly more subtle
because the metric depends on the current schedule state:

* a schedule-dependent canonical-at predicate
* a constructive canonicality decider
* a local repair lemma for one non-canonical time point
* a finite-horizon normalization theorem
* a finite optimality theorem via the shared normalization skeleton

### 難易度

**中**です。
EDF よりも LLF/LST の方が、metric が state-dependent な分だけ少し重いです。

---

A useful way to organize uniprocessor policy results is the following
five-layer structure:

1. policy definition / chooser
2. local chooser properties
3. local repair
4. finite-horizon normalization
5. finite optimality

This structure matches the current EDF and LLF development and should be used
as the standard template for future uniprocessor policies.

---

# Lv.4: 単一CPU repair と normalization

ここでは単一CPU optimality のうち、policy 固有部分と generic 部分を分離して考える。

## 4-1. policy-facing canonicality

証明すべきこと:

* 各 policy で `canonical_at` に対応する局所 canonicality を定義する
* 各 policy で `canonical_before` に対応する prefix canonicality を定義する
* それらが generic な scheduling algorithm-match predicate と同値であることを示す

## 4-2. local repair

証明すべきこと:

* 非 canonical な時刻を 1 点だけ修復する local repair を与える
* repair 後も valid / feasible / J-only / single-CPU が保たれる
* repair 前 schedule と repaired schedule が修復時刻より前で一致する

## 4-3. prefix agreement

証明すべきこと:

* `ChooseAgreesBefore` を各 policy について示す
* candidate source の prefix extensionality と chooser 側の prefix extensionality を接続する

## 4-4. generic normalization の instantiation

すでにある基盤:

* `normalize_to_canonical_generic`

policy ごとにやること:

* `CanonicalRepairSpec` を満たす
* local repair と prefix agreement を与えて generic skeleton を適用する

### 難易度

**中〜やや高い**です。
generic skeleton は共有されるので、難しさは policy ごとの repair と prefix agreement に集中します。

---

# Lv.5: 単一CPU finite optimality pipeline

ここは単一CPU optimality の共通終端であり、
generic infrastructure としてかなり整っている。

## 5-1. finite witness restriction

すでにある基盤:

* target job set `J` への restriction
* single-CPU view への変換

## 5-2. finite normalization

すでにある基盤:

* finite prefix 上で canonicality を得る generic pipeline

policy ごとにやること:

* Lv.4 の obligation を満たして instantiation する

## 5-3. truncation and scheduler bridge

すでにある基盤:

* deadline horizon での truncation
* canonical schedule + idle tail から `scheduler_rel` への bridge

## 5-4. policy-specific optimality instantiation

整理すべきこと:

* EDF はどこまで generic pipeline に載っているか
* LLF/LST はどこまで generic pipeline に載っているか
* 新 policy を追加するとき、どこまでが局所 obligation でどこから先が自動的に流れるか

### 難易度

**中**です。
最難所は共通骨格ではなく、policy-specific repair と chooser 性質です。

---

# Lv.6: 単一CPU trace 全体の性質

## 6-1. trace 由来 schedule の妥当性

* state trace から得た schedule は valid

## 6-2. service と step semantics の一致

* 1ステップ実行で service が 1 増える
* idle なら増えない

## 6-3. weak fairness / finite progress

* RR で ready に残る job は再選択される
* FIFO で順序が trace 全体で保存される

## 6-4. laxity-based progress

* 最小 laxity job が ready に残るなら、適切な仮定の下で service が進む
* 0-laxity job が放置されない
* feasible 仮定のもとで「危険な job を先に走らせる」性質を整理する

### 難易度

**中〜やや高い**です。

---

# Lv.7: partitioned scheduling の合成性

## 7-1. per-CPU valid から global valid

証明すべきこと:

* 各 CPU 上の schedule が valid なら、全体 multicore schedule も valid

## 7-2. service の分解

証明すべきこと:

* partitioned では job の service は割当先 CPU 上の service と一致
* 他 CPU の寄与は 0

## 7-3. completion / deadline 性質の持ち上げ

証明すべきこと:

* 各 CPU 上で期限を守るなら、全体でも守る
* 各 CPU 上で starvation-free なら、全体でもそう

## 7-4. scheduler-specific lifting

* per-CPU EDF を束ねた partitioned EDF
* per-CPU LLF/LST を束ねた partitioned laxity-based scheduler
* per-CPU RR を束ねた partitioned RR
* per-CPU prioritized FIFO など

### 難易度

**やや高いが、かなり現実的**です。

---

# Lv.8: マルチコア共通性質

## 8-1. multicore work-conserving

証明すべきこと:

* runnable job があり、それを走らせられる idle CPU があるなら、無駄に idle しない

## 8-2. multicore determinism

証明すべきこと:

* 同じ global state なら同じ CPU 割当てが得られる
* tie-break を含めて一意

## 8-3. one-copy invariant

証明すべきこと:

* 各 job は任意時刻で高々1箇所にしか存在しない
* current / runqueue / blocked / migrating の分割が保たれる

## 8-4. idle/busy core 基本補題

証明すべきこと:

* busy core では何かが実行される
* idle core の存在と ready set の関係

## 8-5. dynamic-metric scheduling の共通補題

証明すべきこと:

* deadline や laxity のような動的 metric を使っても top-`m` 選択が定義できる
* 再計算によっても no-duplication / determinism が壊れない

### 難易度

**高め**です。

---

# Lv.9: global scheduling の局所仕様

## 9-1. top-m selection の正しさ

証明すべきこと:

* ready set から高々 `m` 個選ぶ
* それらは distinct
* 各 CPU へ矛盾なく割り当てられる

## 9-2. global EDF

* ready job のうち deadline 最小 `m` 個を選ぶ
* より遅い deadline job を、より早い deadline job より先に置かない

## 9-3. global prioritized FIFO

* 高 priority job を優先して最大 `m` 個選ぶ
* 同 priority 内 FIFO

## 9-4. global laxity-based scheduling

* ready job のうち laxity 最小 `m` 個を選ぶ
* 0-laxity / minimum-laxity job を後回しにしない
* tie-break を含めた一意性
* dynamic metric を用いても top-`m` 選択が健全

## 9-5. global FIFO / RR

定義は可能ですが、EDF/priority/laxity より少し不自然です。

### 難易度

**高い**です。

---

# Lv.10: 進行性・公平性・bounded waiting

## 10-1. partitioned での進行性

* 各 CPU 上の進行性から全体へ持ち上げる
* RR の bounded waiting を CPU ごとに示す

## 10-2. global RR / fair queue 系

証明すべきこと:

* ready に残り続ける job は繰り返し service を受ける
* bounded service gap

## 10-3. priority 系の starvation 条件付き議論

証明すべきこと:

* 高 priority 飽和がなければ低 priority も eventually run
* ある workload 制約の下で starvation-freedom

## 10-4. EDF 系の progress

* finite ready set なら service が進む
* feasibility 仮定の下で miss-free を導く準備

## 10-5. laxity-based 系の progress

証明すべきこと:

* minimum-laxity job が危険域で放置されない
* 0-laxity job の優先実行
* 有限 ready set の下での進行性
* starvation 条件付き議論
* EDF と一致する条件の整理

### 難易度

**高い**です。

---

# Lv.11: busy interval / interference / response time

## 11-1. partitioned response time

* 各 CPU 上で単一CPU解析
* 全体へ合成

## 11-2. global interference 基本補題

証明すべきこと:

* ある job が受ける干渉の上界
* top-`m` 競合の上界
* carry-in 的な先行負荷の定式化

## 11-3. multicore busy interval / busy window

証明すべきこと:

* ある期間、十分多くの CPU が埋まっている
* idle core の不在と干渉量の関係

## 11-4. response time / tardiness

証明すべきこと:

* finish time が定義できる
* 応答時間上界または tardiness bound

## 11-5. laxity-based interference

証明すべきこと:

* laxity-driven preemption が干渉へどう反映されるか
* dynamic priority / dynamic laxity に基づく busy-window 補題
* LLF/LST の十分条件または反例

### 難易度

**非常に高い**です。

---

# Lv.12: schedulability / sufficient tests

## 12-1. partitioned schedulability

* 各 CPU が feasible なら全体 feasible
* per-CPU EDF, per-CPU fixed-priority, per-CPU prioritized FIFO, per-CPU LLF/LST など

## 12-2. global EDF schedulability

候補:

* simple sufficient conditions
* bounded tardiness
* workload-based tests
* speedup-bounded guarantees

## 12-3. global laxity-based schedulability

候補:

* simple sufficient conditions
* EDF と一致する特殊場合
* bounded tardiness 的結果
* 非最適性や過剰 preemption の反例整理

## 12-4. RR / FIFO 系の期限保証

* finite job set なら全完了
* bounded response under assumptions
* soft real-time 的 bound

### 難易度

**非常に高い**です。

---

# Lv.13: 最適性・比較定理・speedup bound

## 13-1. partitioned vs global 比較

* partitioned が単一CPU理論に還元できる
* global はより柔軟だが解析が難しい

## 13-2. global EDF の性能保証

* bounded tardiness
* speedup bound
* resource augmentation 的結果

## 13-3. policy comparison

たとえば:

* RR は FIFO より fairness が高い
* prioritized FIFO は priority respect を最大化する
* EDF は deadline 順序に関して優越する
* laxity-based は危険 job を早く拾うが、解析と preemption は重くなる

## 13-4. EDF と laxity-based の比較

証明すべきこと:

* 一致する条件
* 分岐する条件
* 反例比較
* optimum / non-optimum をどう位置づけるか

### 難易度

**かなり高い**です。

---

# 現実的なおすすめ順序

## 第1段階

* Lv.0 共通基盤
* Lv.1 multicore schedule 健全性
* Lv.2 抽象 scheduler 健全性

## 第2段階

* Lv.3 単一CPU policy 局所仕様
* Lv.4 単一CPU repair と normalization
* Lv.5 単一CPU finite optimality pipeline

このとき EDF と LLF/LST は並行ではなく、

1. EDF を metric-min chooser の最初のインスタンスとして固める
2. その後 laxity を 2つ目のインスタンスとして入れる

のがよい。

## 第3段階

* Lv.6 単一CPU trace 全体性質
* Lv.7 partitioned 合成性

## 第4段階

* Lv.8 multicore 共通性質
* Lv.9 global policy 局所仕様

## 第5段階

* Lv.10 進行性・公平性
* Lv.11 response time / interference

## 第6段階

* Lv.12 schedulability
* Lv.13 performance guarantees

## 第7段階

* Lv.12 OS 寄り operational semantics
* Lv.13 refinement

---

# スケジューラ別に優先すべき証明

## FIFO

優先順位:

1. 単一CPU順序保持
2. partitioned lift
3. finite progress
4. OS queue refinement

## RR

優先順位:

1. 単一CPU rotation
2. bounded waiting
3. partitioned multicore RR
4. timer/quantum correctness
5. per-CPU operational refinement

## Prioritized FIFO

優先順位:

1. lexicographic 選択
2. partitioned priority correctness
3. global top-m priority selection
4. response time / starvation 条件付き解析

## EDF

優先順位:

1. 単一CPU earliest-deadline
2. partitioned EDF
3. global EDF top-m selection
4. interference / schedulability / bounded tardiness
5. performance guarantees

## LLF / LST

優先順位:

1. laxity の定義整合性
2. 単一CPU minimum-laxity chooser
3. 0-laxity job の進行性
4. partitioned laxity-based scheduler
5. global top-m minimum-laxity selection
6. interference / schedulability / 反例整理

---

# まとめ

マルチコア込みで難易度順に並べると、証明すべきことは次のように整理できます。

1. **共通基盤の整合性**
   `service`, `completed`, `ready`, `remaining_cost`, `laxity`, `valid schedule`

2. **マルチコア schedule の基本安全性**
   no-duplication, per-CPU exclusivity, affinity

3. **抽象 scheduler の健全性**
   choose/update の正しさ、不変条件保存、metric-min chooser

4. **単一CPU policy の局所仕様**
   FIFO, RR, prioritized FIFO, EDF, LLF/LST

5. **単一CPU trace 全体性質**
   service 一致、進行性の弱い形、laxity progress

6. **partitioned scheduling の合成性**
   per-CPU 理論から全体理論へ

7. **マルチコア共通性質**
   multicore work-conserving, determinism, one-copy

8. **global scheduling の局所仕様**
   top-m selection, global EDF / priority / laxity-based

9. **公平性・bounded waiting・progress**
   RR, priority, EDF, laxity-based の進行性

10. **interference / response time / busy interval**
    特に global と laxity-based で難しい

11. **schedulability / bounded tardiness / speedup**
    partitioned から始め、global は後

12. **OS 寄り operational semantics**
    migration, wakeup, IPI, timer, preemption

13. **refinement**
    abstract policy と concrete multicore machine の一致
