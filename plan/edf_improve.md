`EDF.v` を確認しました。かなり良いです。いまの実装は、私が前に勧めた **EDF dispatch correctness** の中間目標を、すでにかなり達成しています。

特に `EDF.v` には、

* `readyb` による `Prop` と `bool` の橋渡し
* 候補列から最小 absolute deadline を選ぶ `min_dl_job`
* `choose_edf`
* その正しさとして

  * `choose_edf_ready`
  * `choose_edf_min_deadline`
  * `choose_edf_some_if_exists`

が入っていて、これは `what_to_prove.md` の Lv.2「dispatch 健全性」と Lv.3「EDF の局所仕様」にかなりきれいに対応しています。したがって、**Phase 1 の次の一歩として EDF を入れる**という方針は正しかったといえます。 

いまの位置づけを整理すると、現状はこうです。

* `Base.v` / `Schedule.v` で共通基盤はかなり揃っている
* `PeriodicTasks.v` で job 生成規則の骨格もある
* `EDF.v` で単一CPU policy の最初の1本が入った

なので、ロードマップ上では **「単一CPU共通基盤 → 単一CPU policy 群」へ進み始めた状態**です。これは修正版ロードマップの「最初に完成させるべき核」にかなり沿っています。

ここで次にやるべきことは、もう「EDF を入れるかどうか」ではなく、**EDF を“単発の定理”から“再利用可能な policy モジュール”に引き上げること**です。

## 次に行うべきこと

私のおすすめ順は次です。

### 1. `choose_edf` の前提を明示化する

今の `choose_edf` は「候補列 `candidates` の中から ready なものを filter して最小 deadline を選ぶ」形です。これは最初の実装としてとても良いです。
ただ、将来 `Partitioned` や `Global EDF` に進むときに重要なのは、

* 候補列に重複がない
* 候補列が「その時点の ready set を十分に表している」
* tie-break が deterministic

という前提です。

なので次は、例えば

* `NoDup candidates`
* `forall j, In j candidates <-> eligible ... j`

のような仮定を置いた補題を追加すると、後でそのまま再利用しやすくなります。

### 2. EDF の「局所仕様」をもう少し増やす

いまある3定理はとても良いですが、次の2つを足すと完成度が上がります。

* **候補が全部 not ready なら `choose_edf = None`**
* **候補列が `NoDup` なら、選ばれる job は一意**

前者は `choose_edf_some_if_exists` の反対向きです。
後者は determinism の局所版で、`what_to_prove.md` の「抽象 scheduler の健全性」「determinism」へ自然につながります。 

### 3. `EDF.v` を interface 化する

ロードマップでは `UniSchedulerInterface.v` を置く案になっていました。
今の EDF 実装を見ると、次は

* 単一CPU scheduler の抽象仕様
* その具体実装として EDF

という二層に分けるのが自然です。

たとえば interface 側には、

* returned job is ready
* no ready job is skipped if it has strictly earlier deadline
* exists-ready implies returns-some

のような仕様を置き、`EDF.v` はその実装証明にする形です。

これをやっておくと、FIFO や RR を追加するときに構造が揃います。

## いまの EDF.v の評価

全体として、かなり良いです。特に良い点は3つあります。

1. **`readyb_iff` を最初に証明していること**
   これは filter 系証明で毎回効きます。

2. **`min_dl_job` の補題を独立に切り出していること**
   `min_dl_job_none_iff`, `min_dl_job_in`, `min_dl_job_min` は再利用価値が高いです。

3. **中間目標としてちょうどよい定理をすでに押さえていること**
   `choose_edf_ready` と `choose_edf_min_deadline` は、まさに「簡単なスケジューリング理論の定理」です。`what_to_prove.md` で優先されていた単一CPU EDF の最初の山に相当します。

逆に、今のうちに直したい点もあります。

* `candidates` がただの `list JobId` なので、重複があると「集合」より「列」の意味が強い
* tie-break は実装されているが、仕様としてまだ明文化されていない
* `choose_edf` は dispatch function だが、scheduler state や update はまだない

なので、次は「EDF の選択関数」から「EDF scheduler の仕様」へ1段上げるのがよいです。

## 中間目標としておすすめの定理

今の実装状況を見たうえで、いちばんおすすめなのはこれです。

**EDF local optimality theorem**

形としては、

* `choose_edf ... = Some j`
* `j'` が ready candidate なら
* `deadline j <= deadline j'`

です。

これは実質すでに `choose_edf_min_deadline` で入っています。
なので次の中間目標は、その一歩先の

**EDF completeness theorem**

* 候補列が「ready set を表す」
* ready job が存在する
* なら EDF は必ず選ぶ

と、

**EDF none theorem**

* 候補列内に ready job が存在しない
* なら EDF は `None`

のペアを揃えることです。

この2本が揃うと、EDF は「ready set 上の正しい選択器」としてほぼ完成です。

