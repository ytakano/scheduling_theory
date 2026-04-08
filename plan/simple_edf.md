確認しました。結論からいうと、**次にやるべきことは「単一CPU policy の導入」よりも一段手前の、“共通基盤を使って最初のまとまった定理を一本きれいに立てること”**です。そのうえで、中間目標としては **「有限ジョブ集合に対する EDF の単純な正しさ」** か **「周期タスク生成規則の整合性」** が最もおすすめです。 

現状の実装はかなり良い位置にあります。`Base.v` / `Schedule.v` には、ロードマップ上の Phase 1 に対応する核である `Task`・`Job`・`Schedule`・`service`・`completed`・`ready`・`missed_deadline`・`feasible_schedule`・`feasible` がすでに入っていて、さらに `service` の単調性、1ステップ増分、`completed` と `ready` の整合性、`valid_schedule` から導かれる基本性質まで揃っています。これは `what_to_prove.md` の Lv.0 にかなり対応しています。加えて、`sequential_jobs` もあり、将来のマルチコア no-duplication へ自然につながる形になっています。`PeriodicTasks.v` も、周期タスクを「job生成規則の拡張」として扱う骨格がすでにあり、ロードマップの方針とも一致しています。 

一方で、**まだ手を出さない方がよいもの**もはっきりしています。
いまの段階では、global scheduling、OS寄り operational semantics、refinement、DAG は早いです。ロードマップでも、DAG は「job 内部構造の拡張」なので multicore / global 基盤のあと、周期タスクは「job 生成規則の拡張」なので単一CPU基盤のあと、と整理されています。したがって、現時点で最も自然なのは、

1. 共通基盤を使った“見栄えのよい”定理を一本立てる
2. 単一CPU scheduler interface と EDF/FIFO/RR のどれか1つを入れる
3. その後に periodic task の well-formedness を強める

という順です。

### 次に行うべきこと

おすすめ順はこれです。

**第1候補:**
`Schedule.v` の上に、**単一CPU・有限ジョブ集合版の「EDF が ready な中で最小 deadline を選ぶ」定義**を入れる。
そして最初の定理として、

* EDF が選んだ job は ready
* EDF は未release / completed job を選ばない
* EDF は ready job があるなら、その中で最小 deadline を持つものを選ぶ

を証明する。

これは `what_to_prove.md` でいう Lv.2 の dispatch 健全性と Lv.3 の EDF 局所仕様に当たり、ちょうどよい難易度です。

**第2候補:**
`PeriodicTasks.v` を伸ばして、**生成規則の well-formedness** を証明する。例えば、

* 同じ task の `k` 番目 job の release は単調増加
* implicit-deadline task なら deadline = release + period
* 生成された job が `valid_job_of_task` を満たす
* さらに `task_cost > 0` を仮定すれば `valid_jobs` に持ち上げられる

あたりです。これはロードマップが明示している「周期タスク骨格を先に作る」にきれいに一致します。

### 中間目標としておすすめの定理

中間目標にするなら、私は次の3つをおすすめします。

#### 1. 最もおすすめ

**EDF dispatch correctness**

イメージは次です。

* 前提: `m = 1`
* `choose_edf jobs sched t : option JobId` を定義
* 定理:

  * `choose_edf = Some j -> ready jobs 1 sched j t`
  * `choose_edf = Some j -> forall j', ready ... j' t -> deadline j <= deadline j'`
  * ready job が存在すれば `choose_edf` は `Some _`

この定理が良い理由は、
**「スケジューリング理論っぽい」**、**今の基盤に直接乗る**、**後の partitioned EDF に再利用できる** の3点です。`what_to_prove.md` でも EDF の局所仕様は中難度で、先に進む足場として最適です。

#### 2. 一番やさしい

**周期タスク生成の単調性**

例えば、

* `k1 <= k2 -> expected_release ... τ k1 <= expected_release ... τ k2`

や

* implicit deadline なら `expected_abs_deadline = expected_release + period`

です。

これは証明自体が軽く、`PeriodicTasks.v` の流れを強化できます。
ただし、理論的な見栄えは EDF より少し弱いです。
「まず一本通したい」なら非常に良いです。

#### 3. 共通基盤の締めとして良い

**valid schedule implies no execution before release / after completion**

この種の補題はすでにほぼ揃っていますが、これをまとめて

* running implies pending
* pending implies released and not completed
* completed monotone
* sequential_jobs 下で 1 step 増分は高々 1

を一つの節として整理すると、Phase 1 完了を明確にできます。
ただし「中間目標」としては少し地味です。

### どの定理を選ぶべきか

目的別にいうと、

* **最短で一本通したい** → 周期タスク生成の単調性
* **研究の見栄えを良くしたい** → EDF dispatch correctness
* **将来の partitioned / global に最も効く** → EDF dispatch correctness
* **コード整理を優先したい** → 共通基盤補題の整理

です。

私なら、**中間目標は EDF dispatch correctness** にします。
理由は、ロードマップの「単一CPU policy 実装」「単一CPU 共通性質」へきれいにつながり、その後の `Partitioned.v` で per-CPU EDF を合成する話にも直結するからです。`what_to_prove.md` でも、partitioned は最初の現実的なマルチコア到達点と整理されているので、その入口として EDF の局所仕様を先に固めるのが筋が良いです。

### 実際の次の作業案

かなり具体的に書くと、次はこう進めるのが良いです。

1. `UniSchedulerInterface.v` を作る
   `choose : (JobId -> Prop) -> option JobId` のような最小形でよいです。

2. `EDF.v` を作る
   まずは有限集合を簡単に扱うため、最初は
   `ready_jobs : list JobId` を入力にして最小 deadline を返す関数でも十分です。

3. 次の3定理を証明する

   * 選ばれた job は ready
   * 選ばれた job は deadline 最小
   * ready list が空でなければ選択に成功する

4. 余力があれば `PeriodicTasks.v` に

   * `expected_release` 単調性
   * implicit-deadline の簡単な補題
     を追加する

この順なら、ロードマップの Phase 1 → 2 → 3 に素直に沿います。

