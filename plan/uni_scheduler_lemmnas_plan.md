## 目的の明確化

まず `UniSchedulerLemmas.v` の役割を固定します。

このファイルでは、

* EDF 固有の事実
* FIFO 固有の事実
* RR 固有の事実

は入れず、**任意の単一CPU scheduler が interface の仕様を満たすなら成り立つ補題**だけを置きます。

つまり位置づけは、

* `UniSchedulerInterface.v` = 抽象仕様
* `UniSchedulerLemmas.v` = その抽象仕様から導かれる一般定理
* `EDF.v` = 具体実装と、その interface 充足証明

です。

---

## 全体計画

### Phase 1. interface の棚卸し

最初に `UniSchedulerInterface.v` に何が入っているかを整理します。

確認したいのは主に次です。

* `choose` の型
* `ready` との関係をどう仕様化しているか
* 「ready job があれば選ぶ」をどう表現しているか
* 最適性や tie-break を interface に含めているか
* 候補集合を `list JobId` で渡しているか、述語で渡しているか

ここでやることは、**lemma の入力になる仮定を明文化すること**です。

この段階の成果物は、
「この interface から一般補題として何が導けるか」の一覧です。

---

### Phase 2. lemma の分類

次に、入れる lemma を3種類に分けます。

#### A. 選択の健全性

「選ばれたものは正しい」

例:

* 選ばれた job は ready
* 選ばれた job は候補の中にいる
* 選ばれた job は unreleased / completed ではない

#### B. 選択の完全性

「正しい対象が存在すれば選択は失敗しない」

例:

* ready candidate が存在すれば `choose <> None`
* `choose = None` なら ready candidate は存在しない

#### C. 選択の順序性・決定性

「どういう基準で選んでいるか」

これは interface にその仕様があるときだけ入れます。

例:

* 最小 deadline job を選ぶ
* tie-break が一貫している
* 同じ入力なら同じ出力になる

この分類を最初にやっておくと、EDF 以外の policy を追加するときも再利用しやすいです。

---

### Phase 3. 最小版を先に作る

最初から大きくせず、まずは **最小の一般補題セット**を作ります。

おすすめは次の4本です。

1. `choose_some_implies_ready`
2. `choose_some_implies_in_candidates`
3. `ready_exists_implies_choose_some`
4. `choose_none_iff_no_ready_candidate`

この4本が揃うだけで、かなり使えます。

特に 4 は、3 の逆向きも含めて整理できるので便利です。

---

### Phase 4. Section / Context の設計

証明しやすくするために、`UniSchedulerLemmas.v` は `Section` ベースで作るのがよいです。

たとえば必要なのは、

* `jobs : JobId -> Job`
* `sched : Schedule`
* `t : Time`
* `candidates : list JobId`
* `choose : ...`
* interface を満たす仮定

です。

ポイントは、**EDF に依存しない形に保つ**ことです。
`min_dl_job` や deadline 比較の具体実装はここに持ち込まない方がよいです。

---

### Phase 5. interface から直接出る lemma を証明

ここで本体を書きます。

順番は次がよいです。

#### 5-1. `Some` 側

まず「選ばれたら正しい」を証明します。

* `choose ... = Some j -> ...`

この方向は通常証明しやすいです。

#### 5-2. 存在から `Some`

次に

* `(exists j, ...) -> exists j', choose ... = Some j'`

を証明します。

#### 5-3. `None` の特徴づけ

最後に

* `choose ... = None <-> ~ exists j, ...`

を証明します。

これは前の lemma を組み合わせるだけで済むことが多いです。

---

### Phase 6. policy 非依存であることを確認

書いた lemma が

* EDF にしか使えない形になっていないか
* deadline を直接参照していないか
* list の具体的な探索順に依存していないか

を確認します。

もし deadline や priority の話が必要なら、それは `UniSchedulerLemmas.v` ではなく、

* `EDF.v`
* `PrioritizedFIFO.v`

などに置く方が自然です。

---

## おすすめのファイル構成

`UniSchedulerLemmas.v` の中は、次のような章立てがわかりやすいです。

### 1. 基本設定

* import
* section
* context
* interface 仮定

### 2. Soundness lemmas

* chosen job is valid
* chosen job is ready
* chosen job is in candidates

### 3. Completeness lemmas

* ready exists implies choose some
* choose none implies no ready candidate
* choose none iff no ready candidate

### 4. Derived corollaries

* not idle if ready exists
* impossible to choose completed job
* impossible to choose unreleased job

---

## 最初に書くべき lemma 候補

名前は一例ですが、こんな感じがよいです。

* `choose_some_implies_ready`
* `choose_some_implies_in_candidates`
* `choose_some_implies_pending`
* `ready_exists_implies_choose_some`
* `choose_none_implies_no_ready_candidate`
* `choose_none_iff_no_ready_candidate`

もし interface に最適性仕様があるなら追加で

* `choose_optimal`
* `choose_deterministic`

も候補です。

---

## 注意点

注意したいのは3つです。

### 1. `list` と `set` を混同しない

候補を `list JobId` で渡しているなら、

* `In j candidates`

で議論するのか、

* 重複なし `NoDup candidates` を仮定するのか

を最初に決めた方がよいです。

### 2. `ready` を直接使うか、bool 版を使うかを揃える

EDF では `readyb` を使っていたので、一般 lemma 側でも

* `Prop` ベースで進める
* 必要に応じて bool との対応 lemma を別に置く

という整理がよいです。

### 3. interface にないことを勝手に lemma にしない

たとえば
「必ず候補の先頭を選ぶ」
「最小 deadline を選ぶ」
は EDF や FIFO の仕様であって、一般 scheduler の仕様ではありません。

ここを混ぜないのが大事です。

---

## 完成条件

`UniSchedulerLemmas.v` ができたと言える目安は、

* EDF 固有の事実を使わずに証明されている
* 次に FIFO や RR を追加しても、そのまま使い回せる

の2つです。

---

## 実装順のおすすめ

実際の手順としては、次の順がやりやすいです。

1. `UniSchedulerInterface.v` の仕様を箇条書きで整理
2. `choose_some_implies_ready`
3. `ready_exists_implies_choose_some`
4. `choose_none_iff_no_ready_candidate`
5. `choose_some_implies_in_candidates`
6. 必要なら `pending` や `released` への系を追加

---

