これは、ロードマップでいう「各 CPU 性質から全体性質へ」と、`what_to_prove.md` の Lv.5「partitioned scheduling の合成性」をそのまま具体化したものです。

## ゴール

最終ゴールは次の 3 本です。

1. **completion の local/global 対応**
   割当先 CPU 上で completed であることと、global schedule 上で completed であることを対応づける。

2. **deadline miss の local/global 対応**
   各 job の deadline miss が、割当先 CPU の 1CPU view と global schedule で一致することを示す。

3. **feasibility の持ち上げ**
   各 CPU 上で期限を守るなら、全体でも期限を守ることを示す。
   これは partitioned schedulability の最初の到達点です。

---

## Phase 1: まず statement を固定する

最初に、何を theorem として置くかを決めます。おすすめはこの順です。

### 1-1. deadline miss の同値

たとえば次の形です。

* `missed_deadline_on_assigned_cpu_iff`
* 内容:
  `missed_deadline jobs m sched j <-> missed_deadline jobs 1 (cpu_schedule sched (assign j)) j`

これは completion の同値からすぐ落ちる形にしておくときれいです。

### 1-2. feasible_schedule の lifting

次に、

* `local_feasible_implies_global_feasible_schedule`

のような定理を置きます。内容は

* 各 CPU `c < m` について、その `cpu_schedule sched c` が feasible
* `sched` が assignment を守る
* なら global `sched` も feasible

です。

### 1-3. policy-specific corollary

最後に、

* `partitioned_edf_feasible`
* `partitioned_fifo_feasible`

のような系を置きます。
ここでは EDF や FIFO 自体の局所性質を再利用するだけにして、`Partitioned.v` に scheduler 固有の証明ロジックを入れすぎないのが大事です。ロードマップでも partitioned は「単一CPU理論の再利用」が主眼です。

---

## Phase 2: completion から deadline への橋を作る

ここは一番簡単で、先に済ませるべき部分です。

### 2-1. completed の同値を起点にする

すでに `service` の分解と `completed` の local/global 対応があるなら、その上に deadline miss を載せます。
deadline miss は「deadline 時点で未完了」で定義されるので、completion の同値からほぼ 1 行で出せるはずです。`what_to_prove.md` でも partitioned ではまず `service` の分解、次に `completion / deadline` の持ち上げ、という順になっています。

### 2-2. ここで done とする条件

この段階の完了条件は、

* 任意の job `j` について
* `assign j` 上の 1CPU view で missed すること
* global で missed すること

が同値になっていることです。

---

## Phase 3: feasible_schedule の lifting を証明する

ここがこの作業の中心です。

### 3-1. まず schedule 単位で証明する

先にやるべきは `feasible_schedule` の lifting で、`feasible` の existential な定理は後回しでよいです。
つまり、

* ある具体的な global schedule `sched`
* 各 CPU の local view が feasible
* なら global feasible

を示します。

これは `feasible` より扱いやすいです。`what_to_prove.md` でも Lv.5 の段階ではまず schedule の合成性をやるのが自然です。

### 3-2. proof skeleton

proof の流れは次の通りです。

* 任意の `j` をとる
* `assign j = c` とおく
* 仮定より `cpu_schedule sched c` は feasible
* よって `j` は local で missed しない
* deadline miss の同値より global でも missed しない
* よって global feasible

この証明は job ごとに assignment 先 CPU を 1 個選べることに依存します。これは partitioned の本質です。

### 3-3. 注意点

ここで一つだけ設計上の確認が必要です。
もし現在の `feasible_schedule` が **全 `JobId` を量化する total-function 版**なら、`xs` に含まれない job や「その CPU scheduler が候補として見ていない job」をどう扱うかを整理しておく必要があります。

そのため、次のどちらかにすると安全です。

* まずは `feasible_schedule_on` のような **対象 job 集合つき版**で証明する
* あるいは `xs` が対象 job 集合を完全に cover する仮定を追加する

この点は先に決めておくと、あとで定理の statement を作り直さずに済みます。

---

## Phase 4: feasible への持ち上げ

`feasible_schedule` が済んだら、existential な `feasible` へ進みます。

### 4-1. theorem の形

たとえば

* 各 CPU ごとに local feasible schedule がある
* それらを pointwise union した global schedule を作る
* その union が valid かつ feasible

を示します。

### 4-2. ただし後回しでよい理由

これは少し重いです。
なぜなら

* local schedule の family をどう受け取るか
* global union をどう定義するか
* validity と feasibility を両方まとめて示すか

を決める必要があるからです。

なので、まずは **既にある global `sched` に対する lifting** を完成させ、その次に existential な `feasible` に進むのがよいです。

---

## Phase 5: EDF / FIFO への接続

partitioned の一般定理ができたら、ようやく policy-specific corollary を付けます。

### 5-1. EDF

最初は EDF がよいです。
理由は、優先順位表でも EDF は

1. 単一CPU earliest-deadline
2. partitioned EDF
3. global EDF

の順で進めるのが推奨されているからです。

ここでやることは、

* 各 CPU 上の local scheduler が EDF spec を満たす
* よって各 CPU 上の schedule が local に valid / feasible
* partitioned lifting により global に valid / feasible

という流れです。

### 5-2. FIFO

FIFO も同じ形で付けられます。
ただし FIFO は hard real-time の deadline guarantee より、まず順序保持や finite progress の方が自然なので、deadline 系の系は EDF の後でもよいです。

### 5-3. RR はまだ後

RR は優先順位表でも

1. rotation
2. bounded waiting
3. partitioned multicore RR

の順なので、今はまだ入れなくてよいです。

---

## Phase 6: 進捗確認用の中間目標

途中で止まっても意味があるように、マイルストーンを切るとこうなります。

### M1

`Partitioned.v` に

* deadline miss の local/global 同値
  が入る。

### M2

`Partitioned.v` に

* local feasible schedule -> global feasible schedule
  が入る。

### M3

`Partitioned.v` または `EDF.v` 側に

* partitioned EDF の基本系
  が入る。

### M4

必要なら job 集合つき (`..._on`) の定理を整えて、有限集合ベースの議論に進める。

---

## 実装順のおすすめ

一番実装しやすい順に並べると、こうです。

1. `missed_deadline` の local/global 同値
2. `~missed_deadline` の local/global 同値
3. `feasible_schedule` の lifting
4. 必要なら `feasible_schedule_on` 版の導入
5. `feasible` の existential lifting
6. `partitioned EDF` の系
7. `partitioned FIFO` の系

---

## この plan の狙い

この plan のよいところは、`Partitioned` を **「単一CPU理論を全体へ持ち上げる層」**として明確に保てることです。
ロードマップでも、partitioned scheduling は「assign function」「per-CPU scheduler lifting」「各 CPU 性質から全体性質へ」が中心で、global scheduling や OS operational semantics より前に完成させるべき核として置かれています。
