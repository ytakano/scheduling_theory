# Awkernel 2 CPUs Workload Refinement

このメモは、Awkernel の 2 CPU async/await workload trace を、RocqSched の
既存の operational boundary へつなぐときに、実際にどの順で何を行い、
どの artifact をどこで確認しているかをまとめる手順書である。
ここで扱うのは common layer の拡張ではなく、Awkernel adapter layer と
concrete runtime layer の narrow な refinement 手順である。

この手順の目的は次である。

- Awkernel が emit した workload trace を serial log として取得する
- その log から rows と lifecycle block を取り出し、
  Haskell acceptance lane で concrete trace constraint を判定する
- concrete trace checking と generic refinement obligation を分離した現行境界を記録する

この手順の範囲外にあるものは次である。

- all Awkernel traces の被覆
- IPI, timer interrupt, preemption, migration を含む一般 trace family
- scheduler-relation
- ideal scheduler policy との一致
- bounded-delay / deadline 保証

## Procedure Overview

### 1. Abstract interface

保持する abstract interface は既存の operational common layer である。

- `OpState`
- `OpEvent`
- `OSProjection`
- `OSLabeledProjection`
- `OSLocalAdapterContract`

workload trace のために common layer へ新しい event や state field は追加しない。
追加するのは Awkernel adapter-local checker と、runtime-local lifecycle export
だけである。

### 2. Concrete behavior

Awkernel runtime は 2 CPU 上で async/await workload を実行し、
baseline、rows、lifecycle、Rocq-export block を埋め込んだ serial log を emit する。

このうち semantic acceptance の主入力は、log から抽出した

- rows
- lifecycle

の 2 つである。baseline text と generated Rocq export は regression/reference
artifact としてだけ使う。

### 3. Layer split

#### Common layer

既存の operational interface と projection obligations を提供する。
workload-specific な spawn, sleep, join などの concrete executor detail は
ここへ持ち込まない。

#### Adapter layer

Awkernel emitted rows と lifecycle export から、
`accepted workload trace` かどうかを判定する generation-rules checker を置く。
この checker の定義は `Operational/Awkernel/Minimal/WorkloadAcceptance.v` にあるが、
実際の concrete trace constraint 判定は、その Haskell 抽出が acceptance lane で実行する。
Rocq 側は accepted trace を既存の replay/projection path へ入れるための
generic refinement obligation を持つ。

#### Concrete runtime layer

Awkernel async executor の spawn / runnable / choose / dispatch / sleep /
join-wait / complete を lifecycle artifact として emit する。
また scheduler-visible rows を baseline trace hook から抽出する。

## Step 1: runtime が rows と lifecycle を出力する

まず runtime で、既存の baseline trace に加えて task lifecycle export を記録する。
この段階で差し込むのは、後段の checker が finite task set と
scheduler-visible state を復元するために必要な concrete event source だけである。
現在の主な差し込み点は次である。

- task spawn
- task becomes runnable
- scheduler choose
- scheduler dispatch
- task sleep
- join wait
- task complete

これらは `awkernel_async_lib` の executor / task / sleep / join_handle 側から
`baseline_trace::record_lifecycle(...)` を呼ぶ形で記録される。
workload trace 用 feature が有効なときだけ有効になり、通常 runtime path には
影響を与えない。

workload trace VM では root orchestrator task を起動し、
`arm_dump_on_complete(root_task_id)` によって root task の完了時に dump を
1 回だけ行う。したがって、この段階で得られるのは「workload 全体が終了した時点の
deterministic artifact」である。

現在の representative workload は 4 つである。

- `single_async_trace_vm`
- `nested_spawn_trace_vm`
- `multi_async_trace_vm`
- `sleep_wakeup_trace_vm`

これらは semantic family の定義ではなく、runtime artifact を出す
representative examples である。

## Step 2: acceptance lane が lifecycle summary を構成する

次に acceptance lane が lifecycle export を読み、finite task set と dependency を
recover する summary を作る。ここで使うのは `rows + lifecycle` を受ける
adapter-local checker の Haskell 抽出であり、common layer の interface は広げない。

現在の checker の定義は `Operational/Awkernel/Minimal/WorkloadAcceptance.v` にあり、
実際の concrete artifact に対する summary 構成は extracted checker が行う。

この summary では、まず lifecycle export を読み、次の情報を構成する。

- root task
- known tasks
- completion dependencies

lifecycle record として現在扱う kind は次である。

- `Spawn`
- `Runnable`
- `Choose`
- `Dispatch`
- `Sleep`
- `JoinWait`
- `Complete`

この段階では、task が存在する前に参照されていないか、
join wait が既知 task 間で張られているか、known task 集合に重複がないか、
といった well-formedness を確認する。
この lifecycle summary が、現在の finite task universe の authoritative source
である。

## Step 3: acceptance lane が rows を finite-task summary と照合する

その後 scheduler-visible rows を読み、Step 2 で得た summary と照合しながら
row-state machine を進める。現在の checker は fixed job-id example に依存せず、
lifecycle summary から復元した known task 集合の上で row matching を行う。
このとき runnable list の順序自体は意味論に使わず、membership だけを使う。

現在見る row pattern は次である。

- wakeup row
- choose row
- dispatch row
- complete row
- optional stutter row

checker state には少なくとも次を持つ。

- trace started かどうか
- currently selected task
- already dispatched tasks
- already completed tasks

現在の受理器は、

- root task の wakeup から開始する
- known task 以外は choose / dispatch / complete できない
- duplicate spawn を許さない
- invalid join edge を許さない
- sleeping / join dependency に反する completion を許さない
- `cpu=1`, `current=None`, `need_resched=false`, `dispatch_target=None` の
  narrow shape に限って optional stutter を許す
- trace 末尾で root task が completed に入っている

ことを要求する。

## Step 4: acceptance lane が extracted checker を実行する

checker は Rocq で定義され、Haskell へ Extraction される。実際の運用では
checker を source のまま使うのではなく、extracted checker を serial log に
対して実行する。concrete trace constraint の判定は acceptance lane に集約し、
Rocq 側で実トレースを個別に再検査しない。

現在の active path は次である。

- Rocq source:
  `Operational/Awkernel/Minimal/WorkloadAcceptance.v`
- Extraction entry:
  `Operational/Awkernel/Minimal/WorkloadAcceptanceExtraction.v`
- Extracted module:
  `scheduling_theory/extracted/haskell/AwkernelWorkloadAcceptance.hs`
- Haskell runner:
  `awkernel/scripts/haskell/WorkloadAcceptanceMain.hs`
- Python wrapper:
  `awkernel/scripts/check_workload_acceptance.py`

Haskell 側の active path は serial log から抽出された

- rows TSV
- lifecycle TSV

を読み、extracted checker `awk_workload_accepts_trace lifecycle rows` を呼ぶ。
現在の active acceptance lane は、成功時に proof-facing artifact を出力しない。
返すのは `accept/reject` と diagnostics だけである。

現在の failure split は次である。

- rows block が無い
- lifecycle block が無い
- rows parse failure
- lifecycle parse failure
- semantic rejection

## Step 5: QEMU/KVM で trace を取得し、acceptance lane で確認する

次に QEMU または Linux KVM で representative workload trace を取得する。
この段階では、runtime が emit した serial log から rows と lifecycle を抽出し、
acceptance lane だけを実行する。

### Acceptance path

`check-workload-accept-*` は、生ログから

- `BEGIN_TRACE_ROWS ... END_TRACE_ROWS`
- `BEGIN_TASK_LIFECYCLE ... END_TASK_LIFECYCLE`

を抽出し、Haskell checker に渡して semantic acceptance を行う。
この path が concrete trace constraint の semantic oracle である。
成功時には `accept` を返し、失敗時には constraint 種別と場所つきの
diagnostics を返す。成功時に repo 管理下の artifact を追加出力しない。

current runtime capture path は `awkernel/Makefile` にある。

代表的な target は次である。

- `capture-workload-log-qemu-2cpu`
- `capture-workload-log-kvm-2cpu`
- `check-workload-accept-qemu-2cpu`
- `check-workload-accept-kvm-2cpu`

QEMU と KVM はどちらも acceptance backend であり、current workflow では
checked-in workload fixture を保持しない。

## Step 6: acceptance outcome を refinement から分離して解釈する

この手順で得られるのは、`accepted emitted workload artifact` が Awkernel
adapter-local な accepted family に属する、という bool 判定と diagnostics である。
ここでの役割は `concrete trace checking lane` を閉じることであって、
そのまま proof-facing artifact を受け渡すことではない。

この手順が現在保証する境界は次である。

- emitted rows/lifecycle が adapter-local generation rules に従う
- acceptance lane の成功と failure が concrete trace constraint に対して定義されている

この手順ではまだ次を保証しない。

- all valid runtime traces を checker が完全に受理すること
- accepted trace から generic local adapter contract を end-to-end で作ること
- candidate-source や scheduler-relation をこの family 全体で与えること

## 現在の到達点

現在、この 2 CPU workload refinement path でできているのは次である。

- runtime が rows + lifecycle artifact を deterministic に emit する
- extracted Haskell checker がその artifact を受理/棄却できる
- KVM でも smoke acceptance を回せる

## この手順の現在の限界

この手順がまだ扱わないものは次である。

- all Awkernel traces を含む workload family
- accepted workload trace からの generic candidate-source reuse
- dispatch-latency gap を吸収する scheduler-facing witness
- scheduler-relation
- bounded-delay / deadline proof

現在の checker は fixed job-id の例に依存せず、lifecycle summary が与える
known task 集合の上で row matching を行う。この段階での主張は
`current lifecycle-grammar family が受理する任意の有限 task set` に限られ、
Awkernel が emit しうる全 trace の coverage を意味しない。

## この手順の先にある拡張

この節では、Step 1 から Step 6 の procedure 本体の先に置く後続拡張だけを記録する。
ここから先は、現在実際に回している手順ではなく、その accepted family を
次の refinement reuse へ接続するための段階である。

旧 draft の Step 7 にあった rows-only candidate-table generation / checking は、
現在は Step 4 と Step 5 の acceptance lane に吸収されている。

## Future Step 8: generic local refinement obligations

Step 6 の bool-valued acceptance boundary の後段では、Rocq が concrete trace を
個別に再検査するのではなく、acceptance decision procedure に対する generic
soundness/completeness theorem と、その accepted family に対する generic local
refinement obligations を扱う。この step は adapter layer の内部にとどまり、
common layer の event/state interface は増やさない。

## Future Step 9: scheduler-facing witness

Future Step 8 の後段では、dispatch-latency gap を吸収する adapter-local
scheduler-facing witness を導入する。この witness の役割は、accepted family に
対する後段の proof obligation を与えることであり、common operational interface
自体を変更することではない。

## Future Step 10: scheduler-relation

scheduler-relation は、Future Step 9 のさらに後段で扱う。したがって、この文書の
Step 1 から Step 6 は現在の procedure、Future Step 8 以降はその先にある番号付き拡張である。
