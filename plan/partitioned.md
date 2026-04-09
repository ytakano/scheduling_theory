現状の評価です。

* **Phase 1 の共通基盤**はかなり進んでいます。ロードマップ上の核である `Task` / `Job` / `Schedule` / `service` / `completed` / `ready` / `feasible` を先に固める方針に沿っていて、全体の順序としては良いです。
* **単一CPU scheduler 抽象化と EDF の局所仕様**も進んでいます。`UniSchedulerInterface.v` と `UniSchedulerLemmas.v`、`EDF.v` があるので、ロードマップの「単一CPU policy 実装」と「単一CPU 共通性質」の一部まで入っています。これは難易度表でいう Lv.0〜Lv.3 をかなり消化している状態です。
* **周期タスク**は、ロードマップが言う「job 生成規則の拡張」の骨格がすでに入っています。なので、周期タスクを今すぐ主戦場にする必要は薄いです。
* 一方で、ロードマップが次の山として推している **partitioned scheduling** はまだ未実装です。しかも難易度表でも、最初の現実的なマルチコア成果としてここを狙うのがよいとされています。

実装を見た上での、いちばん重要な所見もあります。

**今の `UniSchedulerSpec` は名前ほど汎用ではなく、実質 EDF 寄りです。**
理由は、抽象 interface に `choose_min_deadline` が入っているからです。これだと FIFO / RR / prioritized FIFO はそのままではこの interface を満たせません。つまり、ロードマップが想定している「FIFO, RR, prioritized FIFO, EDF を共通基盤の上で並べる」構成と、今の interface には少しズレがあります。ロードマップ自体も、抽象 interface は分けた方がよいとしています。

なので、次に行うべきタスクは、ひとことで言うと

**「partitioned scheduling に進むための interface 整理 + Partitioned.v の実装」**

です。

おすすめの plan はこれです。

### 1. まず interface を 2 層に分ける

目的は、EDF 専用性を generic 層から外すことです。

* **汎用 dispatch interface**

  * chosen job is ready
  * ready job があれば `Some`
  * ready job がなければ `None`
  * chosen job は candidate に属する
* **policy-specific interface**

  * EDF: minimum deadline
  * FIFO: 先頭保持
  * RR: rotation
  * prioritized FIFO: 優先度 + FIFO

これで `UniSchedulerLemmas.v` も

* 汎用補題
* EDF 専用補題
  に分けやすくなります。

### 2. `Partitioned.v` を作る

ロードマップどおり、まずは partitioned を最初のマルチコア目標にします。

ここで入れるべき定義は、

* `assign : JobId -> CPU`
* `assigned_to j c`
* 各 CPU の candidate 集合
* 各 CPU で単一CPU scheduler を回し、それを合成した全体 schedule

です。

### 3. 最初の core theorem を 3 本に絞る

`Partitioned.v` の最初の到達点としては、次の 3 本がちょうどよいです。難易度表の Lv.5 と一致しています。

* **assignment respect**
  実行された job は必ず割当先 CPU 上でのみ走る
* **global validity from local validity**
  各 CPU 上の local schedule が valid なら、合成した multicore schedule も valid
* **service decomposition**
  partitioned では job の service は割当先 CPU の service と一致し、他 CPU の寄与は 0

この 3 本ができると、partitioned EDF / partitioned RR / partitioned prioritized FIFO にそのまま伸ばせます。

### 4. その後に `partitioned EDF` を具体化する

EDF はすでに局所仕様があるので、最初の具体 policy として最も自然です。難易度表でも EDF の次の優先順位は partitioned EDF です。

ここでは、

* per-CPU EDF chooser を使った partitioned schedule
* `valid_schedule` の持ち上げ
* `feasible_schedule` の CPU ごとの分解

まで行けば十分です。
この段階では、まだ本格的な schedulability test まで行かなくてよいです。

---

## 結論

次の 1 タスクに絞るなら、

**`Partitioned.v` を作る前提として、`UniSchedulerInterface.v` を「汎用 dispatch spec」と「EDF-specific spec」に分離し、そのうえで partitioned EDF の validity 合成を証明する**

のが最善です。

理由は 3 つです。

* ロードマップが、次の現実的マイルストーンとして partitioned を強く推している。
* 今の実装は共通基盤・EDF・周期タスク骨格まであるので、ちょうどそこへ届く土台がある。
* ただし interface が EDF 特化ぎみなので、そのまま進むと FIFO/RR/prioritized FIFO へ広げにくい。ロードマップの「抽象 interface の分離」とも合う。
