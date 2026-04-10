# `UniSchedulerBundle` 導入計画

この plan の狙いは、

* chooser
* candidate source の健全性
* abstract policy
* policy sanity
* refinement

を 1 つの bundle にまとめ、
**単一CPU scheduler の標準的な「実装パッケージ」**として使えるようにすることです。

一方で、

* `valid_schedule`
* `schedulable_by_on`
* concrete scheduler から abstract policy scheduler への導出

は bundle の field にせず、**一般補題で導出する**方針を保ちます。

---

# 全体方針

導入は次の 4 段階に分けるのが安全です。

1. **bundle を定義する**
2. **bundle から scheduler / policy scheduler を作る共通導線を作る**
3. **EDF を bundle 化する**
4. **FIFO など他 policy に展開する**

重要なのは、最初から既存の EDF/FIFO の定義を全部壊さないことです。
まずは **既存実装の上に bundle を薄く被せる** 形で導入し、その後必要なら古い入口を整理します。

---

# Phase 1: `UniSchedulerBundle` を導入する

## 目的

単一CPU policy 実装の最小パッケージを record として固定する。

## 作業

`UniSchedulerInterface.v` に、まず以下を置きます。

* `CandidateSource`
* `CandidateSourceSpec`
* `single_cpu_dispatch_schedule`
* `single_cpu_dispatch_scheduler_on`
* `UniSchedulerBundle`

ここでは bundle の field は**最小限**にします。

つまり、導入するのは本当に次だけです。

* 候補集合
* chooser を含む dispatch spec
* 候補集合の健全性
* abstract policy
* policy sanity
* refinement 証明

## この段階でやらないこと

* `Program` を使った obligations 整理
* typeclass 化
* EDF/FIFO の全面書き換え
* `DispatchSchedulerBridge.v` の削除

## 完了条件

`UniSchedulerBundle` が単独で定義され、他ファイルが import できる。

---

# Phase 2: bundle から共通オブジェクトを導出する

## 目的

bundle を作るだけで、利用者がすぐ scheduler と policy scheduler を得られるようにする。

## 作業

`UniSchedulerLemmas.v` などに、bundle から作る共通定義を追加します。

まず必要なのはこの 2 つです。

### 1. concrete scheduler

```coq
Definition uni_scheduler_on
    {J : JobId -> Prop}
    (B : UniSchedulerBundle J)
    : Scheduler := ...
```

これは `usb_spec`, `usb_candidates`, `usb_candidates_ok` から
`single_cpu_dispatch_scheduler_on` を作るだけです。

### 2. abstract policy scheduler

```coq
Definition uni_policy_scheduler_on
    {J : JobId -> Prop}
    (B : UniSchedulerBundle J)
    : Scheduler := ...
```

これは `usb_policy` と `usb_candidates` から
`single_cpu_policy_scheduler` を作る定義です。

## 次に入れる共通補題

この段階では、最低限以下で十分です。

* `uni_scheduler_on_valid`
* `uni_scheduler_on_refines_policy`

ここで重要なのは、`validity` を bundle field にしない代わりに、

* `usb_spec`
* `usb_candidates_ok`

から validity が出る

ことを一般補題として固定することです。

## 完了条件

bundle を渡せば

* executable scheduler
* abstract policy scheduler
* validity
* refinement による橋
  が共通定義/共通補題で使える。

---

# Phase 3: EDF を bundle instance にする

## 目的

新しい bundle 設計が本当に使えることを、EDF で確認する。

## 作業

`UniPolicies/EDF.v` に、既存の

* `edf_generic_spec`
* `edf_policy`
* `edf_policy_sane`
* `choose_edf_refines_edf_policy`

を使って、最後に `edf_bundle` を定義します。

形としては、

```coq
Definition edf_bundle
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (cand_spec : CandidateSourceSpec J candidates_of)
  : UniSchedulerBundle J := ...
```

です。

そして、bundle から作る thin wrapper として

* `edf_scheduler_on`
* `edf_policy_scheduler_on`

を追加します。

つまり EDF は今後、

* chooser 単体
* generic spec
* abstract policy
* refinement
* bundle
* scheduler wrapper

という層で読めるようにします。

## 注意

この段階では、既存の `edf_scheduler` 的な定義があるなら、**残してよい**です。
まずは互換性を保ったまま bundle 版を足します。

## 完了条件

EDF が `UniSchedulerBundle` の instance として表現できる。

---

# Phase 4: FIFO を同じ骨格に揃える

## 目的

bundle が EDF 専用でないことを確認する。

## 作業

`UniPolicies/FIFO.v` に対しても、EDF と同じ骨格で

* `fifo_bundle`
* `fifo_scheduler_on`
* `fifo_policy_scheduler_on`

を追加します。

この時点で EDF と FIFO の末尾構造がほぼ同じになっているのが理想です。

## 完了条件

少なくとも 2 つの policy が同じ bundle interface に載る。

---

# Phase 5: 既存 bridge/refinement 導線を bundle ベースに整理する

## 目的

今後 client が `UniSchedulerBundle` を入口として見られるようにする。

## 作業

`DispatcherRefinement.v` や `UniSchedulerLemmas.v` に、bundle ベースの標準補題を追加します。

例えば次のような位置づけです。

* bundle から concrete scheduler を得る
* bundle から policy-valid scheduler を得る
* refinement により前者から後者へ移る
* `schedulable_by_on` へつなぐ

必要なら以下のような補題を揃えます。

* `uni_scheduler_bundle_schedulable_by_on_intro`
* `uni_scheduler_bundle_implies_policy_schedule`
* `uni_scheduler_bundle_valid`

## 完了条件

利用者が policy ごとの細部を知らなくても、bundle から標準導線を使える。

---

# Phase 6: client-facing な入口を bundle に寄せる

## 目的

今後の新 policy 追加を bundle 前提に統一する。

## 作業

新規に書く code/examples では、なるべく

* `*_bundle`
* `uni_scheduler_on`
* `uni_policy_scheduler_on`

を使うようにします。

既存コードはすぐ全部書き換えなくてよいですが、新規コードでは bundle 版を標準入口にします。

## 完了条件

新しい policy を追加するときの雛形が bundle ベースになる。

---

# 実装順をもっと細かく書くと

## Step 1

`UniSchedulerInterface.v` に `UniSchedulerBundle` を追加する

この時点ではまだ unused でもよいです。

---

## Step 2

`UniSchedulerLemmas.v` に

* `uni_scheduler_on`
* `uni_policy_scheduler_on`

を追加する

まずは定義だけでよいです。

---

## Step 3

同じファイルか適切な補題ファイルに

* `uni_scheduler_on_valid`
* `uni_scheduler_on_refines_policy`

を追加する

ここで初めて bundle の意味が立ちます。

---

## Step 4

`UniPolicies/EDF.v` に

* `edf_bundle`
* `edf_scheduler_on`
* `edf_policy_scheduler_on`

を追加する

既存定義は壊さない。

---

## Step 5

`UniPolicies/FIFO.v` にも同じものを追加する

ここで bundle interface が一般的であることを確認する。

---

## Step 6

必要なら `SchedulableExamples.v` などに
bundle ベースの短い使用例を 1 つ追加する

例:

* candidate source を与える
* `edf_bundle`
* `uni_scheduler_on`
* `schedulable_by_on`

この例があると今後かなり使いやすいです。

---

# この plan で大事な判断

## 1. validity は field にしない

これは維持した方がよいです。

理由:

* 既存の一般補題で出せるなら冗長
* policy ごとに validity を毎回保持させる必要がない

つまり bundle は
**「何を持てば scheduler が作れるか」**
だけを表すのがよいです。

---

## 2. refinement は field にする

これは bundle に持たせる価値があります。

理由:

* policy ごとに証明内容が違う
* EDF/FIFO/RR の本質的差分がここに現れる

---

## 3. まず record、typeclass は後

今回の導入では typeclass まで入れなくてよいです。

record だけで十分に効果があります。
typeclass は、bundle ベースの設計が安定してから、
必要なら補助的に追加するのが安全です。

---

# 推奨コミット列

一番安全なのはこの順です。

### Commit 1

`UniSchedulerBundle` を `UniSchedulerInterface.v` に追加

### Commit 2

`uni_scheduler_on` / `uni_policy_scheduler_on` を追加

### Commit 3

bundle から validity / policy-validity を導く補題を追加

### Commit 4

`edf_bundle` と wrapper を追加

### Commit 5

`fifo_bundle` と wrapper を追加

### Commit 6

example を 1 つ bundle ベースにする

---

# レビュー観点

この導入のあと、レビューでは次を見ます。

## 観点1

bundle が薄いまま保たれているか
field が増えすぎていないか

## 観点2

`SchedulerValidity.v` と `DispatcherRefinement.v` の責務が崩れていないか

## 観点3

EDF/FIFO の file structure が揃っているか

## 観点4

将来 RR のような prefix-dependent policy でも bundle に載せられそうか

---

# この導入の次にやるべきこと

bundle 導入が終わったら、次はかなり自然に

**`Partitioned.v` を「CPU ごとの `UniSchedulerBundle` の合成」として整理する**

へ進めます。

その時には、各 CPU ごとに

* local candidate source
* local dispatch spec
* local abstract policy
* local refinement

をまとめて扱えるので、かなり書きやすくなります。
