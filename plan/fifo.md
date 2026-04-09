はい。現状の抽象化に合わせるなら、**FIFO は「candidate list の順序を FIFO 順とみなし、先頭から最初の ready job を選ぶ」**として実装するのが最も自然です。
この方針だと、今の `GenericSchedulerDecisionSpec` にそのまま載りますし、後の **Round Robin の土台**にもなります。

## 実装方針の前提

FIFO には大きく 2 通りあります。

1. **release 時刻最小の job を選ぶ FIFO**
2. **candidate list の先頭から最初の ready job を選ぶ FIFO**

今の設計では、私は **2 を推奨**します。理由は次の通りです。

* `GenericSchedulerDecisionSpec` は「候補集合から 1 つ選ぶ」形なので、**候補列の順序**を活かすのが自然
* Round Robin でも結局 **順序付き ready queue** が必要になる
* EDF のような「優先度関数で最小を選ぶ」型とは別の、**順序ベース policy** の実例になる

つまり、今回の FIFO は
**“ordered ready queue を持つ scheduler の最初の具体例”**
として置くのがよいです。

---

## 目標

次の段階の到達点はこの 2 つです。

* `FIFO.v` を追加し、`fifo_generic_spec : GenericSchedulerDecisionSpec` を作る
* 必要なら FIFO 固有の順序性 lemma まで入れる

---

## 実装 plan

### Phase 0: 先に意味を固定する

最初に FIFO の意味を明文化します。

**推奨定義**

* `candidates` は FIFO 順に並んだ job 列
* `choose_fifo` は `candidates` を先頭から走査し、**最初の ready job** を返す
* `None` は ready な候補が一つもないとき

ここではまだ **non-preemptive FIFO** までは入れません。
今の `GenericSchedulerDecisionSpec` は「選ばれた job は ready」という形なので、まずは **dispatch rule としての FIFO** を作るのがよいです。

---

### Phase 1: 共通 bool bridge を整理する

`EDF.v` にある

* `readyb`
* `readyb_iff`

は FIFO でもそのまま必要になります。
これは policy 非依存なので、先に共通化するのがおすすめです。

**おすすめ配置**

* `Schedule.v` に移す
  あるいは
* `UniSchedulerInterface.v` に移す

私は **`Schedule.v` に寄せる**のが自然だと思います。
`ready` / `eligible` / `running` の bool bridge だからです。

この phase の成果物:

* `readyb`
* `readyb_iff`

を EDF から切り出して共通化

* `EDF.v` はそれを import するだけにする

---

### Phase 2: `FIFO.v` を新設する

新しいファイル `FIFO.v` を作ります。構成は `EDF.v` にかなり寄せてよいです。

#### まず定義するもの

* `choose_fifo`

例えば形としてはこうです。

* `candidates` を先頭から見る
* 先頭 `j` が `readyb = true` なら `Some j`
* そうでなければ残りを再帰

実質的には「最初の ready を返す線形探索」です。

---

### Phase 3: `choose_fifo` の基本補題を証明する

`GenericSchedulerDecisionSpec` を満たすには、まず次の 4 本が必要です。

1. **chosen job is ready**

   * `choose_fifo_ready`

2. **if a ready candidate exists, returns Some**

   * `choose_fifo_some_if_exists`

3. **if no candidate is ready, returns None**

   * `choose_fifo_none_if_no_ready`

4. **chosen job is in candidates**

   * `choose_fifo_in_candidates`

この 4 本が揃えば、`mkGenericSchedulerDecisionSpec` で包めます。

#### ここで使う補助 lemma

必要になりやすいのは次です。

* 先頭から探索する関数についての `In` 補題
* 返った job より前の要素はすべて `readyb = false`
* `readyb_iff`

---

### Phase 4: FIFO 固有の性質を 1 本入れる

`GenericSchedulerDecisionSpec` だけでも十分ですが、FIFO らしさを明確にするために、
**policy invariant** を 1 本入れておくのがおすすめです。

最も自然なのはこれです。

#### 推奨 lemma

`choose_fifo_first_ready` のような形:

* `choose_fifo ... candidates = Some j` なら
* `candidates = prefix ++ j :: suffix`
* しかも `prefix` の全要素は ready でない

これがあると、「FIFO は candidate order 上の先頭 ready を取る」という本質がはっきりします。

EDF の `choose_min_deadline` に対応する、FIFO 側の中心補題です。

---

### Phase 5: `fifo_generic_spec` を作る

Phase 3 の 4 補題ができたら、

* `fifo_generic_spec : GenericSchedulerDecisionSpec`

を定義します。

ここまで来れば、`Partitioned.v` など **GenericSchedulerDecisionSpec に依存する層はそのまま FIFO を使える**はずです。

---

### Phase 6: FIFO 固有 interface を作るか判断する

EDF では `EDFSchedulerSpec` があります。FIFO でも必要なら同じように

* `FIFOSchedulerSpec`

を作れます。

ただし、最初は必須ではありません。
まずは

* `fifo_generic_spec` を作る
* FIFO 固有 lemma を `Section FIFOSchedulerLemmasSection` に置く

で十分です。

#### 先に interface 化しなくてよい理由

EDF は「最小 deadline」という強い policy invariant があるので record 化しやすいです。
FIFO はまず

* 先頭 ready を選ぶ

という 1 本の性質を lemma として置けば足ります。
record 化は、その性質を他ファイルで再利用したくなってからでよいです。

---

### Phase 7: 小さい example を 1 つ作る

最後に、簡単な例を 1 個入れるとよいです。

例えば:

* `candidates = [j1; j2; j3]`
* `j1` は未 release
* `j2` は ready
* `j3` も ready

このとき `choose_fifo = Some j2`

のような例です。

これは証明というより、**設計の意図確認**として重要です。

---

## 変更対象ファイル

### 新規

* `FIFO.v`

### 修正候補

* `Schedule.v`

  * `readyb`
  * `readyb_iff`
* `EDF.v`

  * 共通化した `readyb` を使うように整理

### たぶん不要

* `UniSchedulerLemmas.v`
* `Partitioned.v`

FIFO は `GenericSchedulerDecisionSpec` に乗れば、ここは基本触らなくてよいはずです。

---

## 実装順のおすすめ

実際には次の順が一番安全です。

1. `readyb` / `readyb_iff` を共通化
2. `FIFO.v` に `choose_fifo` を書く
3. 4 つの generic 補題を証明
4. `fifo_generic_spec` を作る
5. FIFO 固有 lemma を 1 本追加
6. 小例を作る

---

## 先に証明すべき最小セット

最小限ならこの 5 個で十分です。

* `readyb_iff`（共通）
* `choose_fifo_ready`
* `choose_fifo_some_if_exists`
* `choose_fifo_none_if_no_ready`
* `choose_fifo_in_candidates`

これで FIFO は **実装完了**と言えます。

その次に入れるべきなのは

* `choose_fifo_first_ready`

です。

---

## Round Robin へのつながり

この plan がよい理由の一つは、これがそのまま Round Robin の準備になることです。

FIFO を「順序付き候補列から最初の ready を取る」として実装しておけば、
Round Robin では後で

* queue rotation
* quantum 満了時の末尾移動

を追加する方向に進めます。

つまり、FIFO は単独でも有用ですが、同時に
**“順序付き ready queue 系 scheduler” の基盤実装**
にもなります。

必要なら次に、`FIFO.v` の雛形をそのまま書ける粒度で、
定義名と lemma 名まで含めた **具体的な実装テンプレート** を出します。
