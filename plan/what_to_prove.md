# スケジューリング理論の定理

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

# 全体の見取り図

証明対象は大きく次の順に進みます。

1. **共通基盤の整合性**
2. **単一CPU policy の正しさ**
3. **マルチコア schedule の基本健全性**
4. **partitioned scheduling の合成性**
5. **global scheduling の基本性質**
6. **進行性・公平性・待ち時間**
7. **response-time / schedulability**
8. **optimality / speedup / bounded tardiness**
9. **OS 寄り operational semantics**
10. **refinement**

---

# Lv.0: 共通基盤の定義整合性

ここは単一CPUでもマルチコアでも共通の最下層です。

## 0-1. service の基本補題

証明すべきこと:

* `service` は単調増加
* 1ステップで高々 1 増える
* 実行されたときだけ増える
* 実行されなければ増えない

マルチコア版では「同時に複数CPUで走らない」という仮定の下で、
なお 1 ステップで高々 1 増えることを示します。

## 0-2. completed / ready の整合性

証明すべきこと:

* completed なら ready でない
* release 前には ready でない
* completed は単調
* ready は service/completion と整合する

## 0-3. valid schedule の基本性質

証明すべきこと:

* release 前に走らない
* completed 後に走らない
* 走っている job は ready

### 難易度

**最も低い**です。

---

# Lv.1: マルチコア schedule の基本健全性

ここから単一CPUにはない性質が入ります。

## 1-1. no-duplication

証明すべきこと:

* 同じ時刻に同じ job が複数CPUで走らない

これはマルチコアの最重要基本不変条件です。

## 1-2. per-CPU exclusivity

証明すべきこと:

* 各 CPU は各時刻に高々 1 job しか走らせない

schedule 型に埋め込むなら不要ですが、trace semantics では明示補題が要ることがあります。

## 1-3. affinity / allowed CPU

入れるなら:

* job は許された CPU 上でしか走らない

## 1-4. multicore service の安全性

証明すべきこと:

* migration があっても service は正しく累積される
* CPU 間の移動があっても completion 判定は壊れない

### 難易度

**低いが、単一CPUより一段上**です。

---

# Lv.2: 抽象 scheduler の健全性

ここでは scheduler state / choose / update を対象にします。

## 2-1. dispatch 健全性

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

### 難易度

**低〜中**です。

---

# Lv.3: 単一CPU policy の局所仕様

ここは前回と同じですが、後の partitioned 再利用のために重要です。

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

### 難易度

**中**です。

---

# Lv.4: 単一CPU trace 全体の性質

ここでは step semantics と schedule/service の対応を固めます。

## 4-1. trace 由来 schedule の妥当性

* state trace から得た schedule は valid

## 4-2. service と step semantics の一致

* 1ステップ実行で service が 1 増える
* idle なら増えない

## 4-3. weak fairness / finite progress

* RR で ready に残る job は再選択される
* FIFO で順序が trace 全体で保存される

### 難易度

**中〜やや高い**です。

---

# Lv.5: partitioned scheduling の合成性

ここがマルチコアで最初に狙うべき山です。
partitioned は、単一CPU理論を再利用しやすいからです。

## 5-1. per-CPU valid から global valid

証明すべきこと:

* 各 CPU 上の schedule が valid なら、全体 multicore schedule も valid

ただし:

* assignment が一意
* 他CPUへ勝手に行かない
* no-duplication

が必要です。

## 5-2. service の分解

証明すべきこと:

* partitioned では job の service は割当先 CPU 上の service と一致
* 他 CPU の寄与は 0

## 5-3. completion / deadline 性質の持ち上げ

証明すべきこと:

* 各 CPU 上で期限を守るなら、全体でも守る
* 各 CPU 上で starvation-free なら、全体でもそう

## 5-4. scheduler-specific lifting

* per-CPU EDF を束ねた partitioned EDF
* per-CPU RR を束ねた partitioned RR
* per-CPU prioritized FIFO など

### 難易度

**やや高いが、かなり現実的**です。
マルチコア最初の到達点として最適です。

---

# Lv.6: マルチコア共通性質

ここから global/clustered に近い抽象性が入ってきます。

## 6-1. multicore work-conserving

証明すべきこと:

* runnable job があり、それを走らせられる idle CPU があるなら、無駄に idle しない

これは単一CPU版よりかなり定義が難しいです。

partitioned と global で別定義にするのが安全です。

## 6-2. multicore determinism

証明すべきこと:

* 同じ global state なら同じ CPU 割当てが得られる
* tie-break を含めて一意

## 6-3. one-copy invariant

証明すべきこと:

* 各 job は任意時刻で高々1箇所にしか存在しない
* current / runqueue / blocked / migrating の分割が保たれる

## 6-4. idle/busy core 基本補題

証明すべきこと:

* busy core では何かが実行される
* idle core の存在と ready set の関係

### 難易度

**高め**です。
global/OS 寄り拡張の土台になります。

---

# Lv.7: global scheduling の局所仕様

ここから global ready set から top-`m` を選ぶ理論に入ります。

## 7-1. top-m selection の正しさ

証明すべきこと:

* ready set から高々 `m` 個選ぶ
* それらは distinct
* 各 CPU へ矛盾なく割り当てられる

## 7-2. global EDF

* ready job のうち deadline 最小 `m` 個を選ぶ
* より遅い deadline job を、より早い deadline job より先に置かない

## 7-3. global prioritized FIFO

* 高 priority job を優先して最大 `m` 個選ぶ
* 同 priority 内 FIFO

## 7-4. global FIFO / RR

定義は可能ですが、EDF/priority より少し不自然です。
研究目的に応じて後回しでもよいです。

### 難易度

**高い**です。
単一選択ではなく「複数選択 + 一意性 + 重複排除」が入るためです。

---

# Lv.8: 進行性・公平性・bounded waiting

ここで「いつか動く」「どれくらい待つか」を扱います。

## 8-1. partitioned での進行性

比較的やりやすいです。

* 各 CPU 上の進行性から全体へ持ち上げる
* RR の bounded waiting を CPU ごとに示す

## 8-2. global RR / fair queue 系

証明すべきこと:

* ready に残り続ける job は繰り返し service を受ける
* bounded service gap

## 8-3. priority 系の starvation 条件付き議論

証明すべきこと:

* 高 priority 飽和がなければ低 priority も eventually run
* ある workload 制約の下で starvation-freedom

## 8-4. EDF 系の progress

* finite ready set なら service が進む
* feasibility 仮定の下で miss-free を導く準備

### 難易度

**高い**です。
measure 減少や有限性仮定が必要になります。

---

# Lv.9: busy interval / interference / response time

ここから本格的なリアルタイム理論です。

## 9-1. partitioned response time

比較的現実的です。

* 各 CPU 上で単一CPU解析
* 全体へ合成

## 9-2. global interference 基本補題

証明すべきこと:

* ある job が受ける干渉の上界
* top-`m` 競合の上界
* carry-in 的な先行負荷の定式化

## 9-3. multicore busy interval / busy window

証明すべきこと:

* ある期間、十分多くの CPU が埋まっている
* idle core の不在と干渉量の関係

## 9-4. response time / tardiness

証明すべきこと:

* finish time が定義できる
* 応答時間上界または tardiness bound

### 難易度

**非常に高い**です。
特に global scheduling では急に難しくなります。

---

# Lv.10: schedulability / sufficient tests

ここで deadline 保証へ行きます。

## 10-1. partitioned schedulability

最初に狙うべきです。

* 各 CPU が schedulable なら全体 schedulable
* per-CPU EDF, per-CPU fixed-priority, per-CPU prioritized FIFO など

## 10-2. global EDF schedulability

候補:

* simple sufficient conditions
* bounded tardiness
* workload-based tests
* speedup-bounded guarantees

## 10-3. RR / FIFO 系の期限保証

hard real-time の主流ではないですが、以下は可能です。

* finite job set なら全完了
* bounded response under assumptions
* soft real-time 的 bound

### 難易度

**非常に高い**です。
global の exact test は特に重いです。

---

# Lv.11: 最適性・比較定理・speedup bound

ここは理論の上級編です。

## 11-1. partitioned vs global 比較

証明すべきこと:

* partitioned が単一CPU理論に還元できる
* global はより柔軟だが解析が難しい

これは大定理というより整理補題群です。

## 11-2. global EDF の性能保証

証明すべきこと:

* bounded tardiness
* speedup bound
* resource augmentation 的結果

## 11-3. policy comparison

たとえば:

* RR は FIFO より fairness が高い
* prioritized FIFO は priority respect を最大化する
* EDF は deadline 順序に関して優越する

### 難易度

**かなり高い**です。
複数 scheduler / schedule の比較が必要です。

---

# Lv.12: OS 寄りマルチコア operational semantics

ここからは理論 + OS 状態遷移の橋渡しです。

## 12-1. per-CPU machine invariants

証明すべきこと:

* `current[c]` と runqueue の排他
* blocked / ready / running / completed / migrating の分割
* one-copy invariant

## 12-2. migration correctness

証明すべきこと:

* migration で job が lost しない
* source/destination queue の整合性
* 実行中 job を二重化しない

## 12-3. wakeup / remote wakeup / IPI

証明すべきこと:

* wakeup job が適切な queue / CPU に入る
* resched IPI が必要な CPU に届く
* remote wakeup が policy を壊さない

## 12-4. timer / quantum / preemption

特に RR で重要です。

* quantum 消費が正しく計上される
* timer tick が適切に reschedule を引き起こす
* preemption で service が二重計上されない

### 難易度

**最上位クラス**です。

---

# Lv.13: refinement

最後に、抽象 policy と具体 machine の一致を示します。

## 13-1. partitioned refinement

* per-CPU queue 実装が抽象 partitioned scheduler を実現する

## 13-2. global refinement

* global heap / per-CPU queues + balancing が抽象 global choose を実現する

## 13-3. service refinement

* operational trace 上の実行量 = abstract service

## 13-4. schedule refinement

* machine trace から得た multicore schedule は abstract policy schedule を満たす

### 難易度

**最難関の一つ**です。
抽象層と具体層の両方を理解している必要があります。

---

# 現実的なおすすめ順序

実際に進めるなら、この順序がかなりよいです。

## 第1段階

* Lv.0 共通基盤
* Lv.1 multicore schedule 健全性
* Lv.2 抽象 scheduler 健全性

## 第2段階

* Lv.3 単一CPU policy 局所仕様
* Lv.4 単一CPU trace 全体性質

## 第3段階

* Lv.5 partitioned 合成性

ここが最初のマルチコア成果として非常に良いです。

## 第4段階

* Lv.6 multicore 共通性質
* Lv.7 global policy 局所仕様

## 第5段階

* Lv.8 進行性・公平性
* Lv.9 response time / interference

## 第6段階

* Lv.10 schedulability
* Lv.11 performance guarantees

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

---

# まとめ

マルチコア込みで難易度順に並べると、証明すべきことは次のように整理できます。

1. **共通基盤の整合性**
   `service`, `completed`, `ready`, `valid schedule`

2. **マルチコア schedule の基本安全性**
   no-duplication, per-CPU exclusivity, affinity

3. **抽象 scheduler の健全性**
   choose/update の正しさ、不変条件保存

4. **単一CPU policy の局所仕様**
   FIFO, RR, prioritized FIFO, EDF

5. **単一CPU trace 全体性質**
   service 一致、進行性の弱い形

6. **partitioned scheduling の合成性**
   per-CPU 理論から全体理論へ

7. **マルチコア共通性質**
   multicore work-conserving, determinism, one-copy

8. **global scheduling の局所仕様**
   top-m selection, global EDF / priority

9. **公平性・bounded waiting・progress**
   RR, priority, EDF の進行性

10. **interference / response time / busy interval**
    特に global で難しい

11. **schedulability / bounded tardiness / speedup**
    partitioned から始め、global は後

12. **OS 寄り operational semantics**
    migration, wakeup, IPI, timer, preemption

13. **refinement**
    abstract policy と concrete multicore machine の一致

この順なら、**単一CPU→partitioned→global→OS/refinement** と無理なく積み上げられます。
