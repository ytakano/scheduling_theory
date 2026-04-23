# Awkernel 2 CPUs Workload Refinement

このメモは、Awkernel の 2 CPU async/await workload trace を、RocqSched の
既存の operational boundary へつなぐために何を行っているかをまとめる。
ここで扱うのは common layer の拡張ではなく、Awkernel adapter layer と
concrete runtime layer の narrow な refinement 作業である。

現時点の goal は次である。

- Awkernel が emit した workload trace を deterministic artifact として取得する
- その artifact が adapter-local な generation rules に従っているかを
  Rocq 由来の checker で判定する
- accepted workload trace を、既存の projection / replay / adapter-obligation
  path へ入れるための前段境界として整理する

ここではまだ主張しない。

- all Awkernel traces の被覆
- IPI, timer interrupt, preemption, migration を含む一般 trace family
- scheduler-relation
- ideal scheduler policy との一致
- bounded-delay / deadline 保証

## Goal

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

Awkernel runtime は 2 CPU 上で async/await workload を実行し、次の 4 種の
artifact を emit する。

- `BASELINE_TRACE:*` による baseline text
- `BEGIN_TRACE_ROWS ... END_TRACE_ROWS` による scheduler-visible rows
- `BEGIN_TASK_LIFECYCLE ... END_TASK_LIFECYCLE` による task lifecycle export
- `BEGIN_ROCQ_TRACE ... END_ROCQ_TRACE` による generated Rocq witness export

このうち semantic acceptance の主入力は

- rows
- lifecycle

の 2 つである。baseline text と generated Rocq export は regression/reference
artifact として使う。

### 3. Layer split

#### Common layer

既存の operational interface と projection obligations を提供する。
workload-specific な spawn, sleep, join などの concrete executor detail は
ここへ持ち込まない。

#### Adapter layer

Awkernel emitted rows と lifecycle export から、
`accepted workload trace` かどうかを判定する generation-rules checker を置く。
この checker は `Operational/Awkernel/Minimal/WorkloadAcceptance.v` にあり、
accepted trace を既存の replay/projection path へ入れるための adapter-local
前段境界である。

#### Concrete runtime layer

Awkernel async executor の spawn / runnable / choose / dispatch / sleep /
join-wait / complete を lifecycle artifact として emit する。
また scheduler-visible rows を baseline trace hook から抽出する。

## Step 1: Awkernelへのトレースポイント差し込み

runtime では、既存の baseline trace に加えて task lifecycle export を追加する。
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

また、workload trace VM では root orchestrator task を起動し、
`arm_dump_on_complete(root_task_id)` によって root task の完了時に dump を
1 回だけ行う。

現在の representative workload は 4 つである。

- `single_async_trace_vm`
- `nested_spawn_trace_vm`
- `multi_async_trace_vm`
- `sleep_wakeup_trace_vm`

これらは semantic family の定義ではなく、runtime artifact を出す
representative examples である。

## Step 2: 生成規則

generation rules は Rocq 側で、`rows + lifecycle` を受ける
adapter-local checker として定義する。

現在の checker は `Operational/Awkernel/Minimal/WorkloadAcceptance.v` にあり、
大きく 2 段からなる。

### 2.1 Lifecycle summary

まず lifecycle export を読み、次の summary を作る。

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
join wait が既知 task 間で張られているか、などの well-formedness を見る。

### 2.2 Row acceptance

次に scheduler-visible rows を読み、summary と照合しながら
row-state machine を進める。

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
- sleeping / join dependency に反する completion を許さない
- optional stutter を許す
- trace 末尾で root task が completed に入っている

ことを要求する。

## Step 3: 生成規則チェッカーの健全性境界

この checker が現在意味しているのは、
`accepted emitted workload artifact` が Awkernel adapter-local な narrow family に
属する、ということである。

ここでの健全性境界は次までである。

- emitted rows/lifecycle が adapter-local generation rules に従う
- accepted trace を replay/projection path に入れる前提として使える

ここではまだ次を示していない。

- all valid runtime traces を checker が完全に受理すること
- accepted trace から generic local adapter contract を end-to-end で作ること
- scheduler-relation や candidate-source をこの family 全体で与えること

つまり、checker の位置づけは `proof entry gate` であって、
完全な refinement closure ではない。

## Step 4: 生成規則チェッカーの作成

checker は Rocq で定義され、Haskell へ Extraction される。

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

Haskell runner は serial log から抽出された

- rows TSV
- lifecycle TSV

を読み、extracted checker `awk_workload_accepts_trace lifecycle rows` を呼ぶ。

現在の failure split は次である。

- rows block が無い
- lifecycle block が無い
- rows parse failure
- lifecycle parse failure
- semantic rejection

### 健全性と完全性

現時点で文書化できるのは、健全性・完全性の目標と現在の境界である。

- 健全性:
  checker が受理した artifact は、Awkernel workload trace family の
  narrow accepted fragment に入っている
- 完全性:
  今の checker が intended family を過不足なく受理すること

ただし現状では、checker は still narrow であり、job 数も small finite range に
限定されている。したがって完全性を広い意味で達成したとはまだ言えない。

## Step 5: QEMU, Linux KVMなどで、Awkernelのトレースを取得する

current runtime capture path は `awkernel/Makefile` にある。

代表的な target は次である。

- `capture-workload-log-qemu-2cpu`
- `capture-workload-log-kvm-2cpu`
- `refresh-workload-trace-fixtures-qemu-2cpu`
- `check-workload-trace-qemu-2cpu`
- `check-workload-accept-qemu-2cpu`
- `check-workload-accept-kvm-2cpu`

QEMU は canonical fixture owner であり、
KVM は smoke backend である。

QEMU fixture は現在、

- `awkernel/fixtures/workload_trace/<scenario>/baseline.txt`
- `awkernel/fixtures/workload_trace/<scenario>/rows.tsv`
- `awkernel/fixtures/workload_trace/<scenario>/lifecycle.tsv`
- `awkernel/fixtures/workload_trace/<scenario>/rocq.v`

として保持される。

得られる trace artifact は概略として次の形になる。

1. baseline text
2. scheduler-visible rows
3. task lifecycle TSV
4. generated Rocq witness export

## Step 6: トレースが生成規則に従っているかをチェックする

Step 4 の checker を用いて、Step 5 で取得した emitted workload trace を
acceptance 判定する。

ここでの役割分担は重要である。

### Acceptance path

`check-workload-accept-*` は、生ログから

- `BEGIN_TRACE_ROWS ... END_TRACE_ROWS`
- `BEGIN_TASK_LIFECYCLE ... END_TASK_LIFECYCLE`

を抽出し、Haskell checker に渡して semantic acceptance を行う。
これは fixture equality に依存しない。

### Regression path

`check-workload-trace-qemu-2cpu` は QEMU fixture と比較して、

- baseline text
- rows
- lifecycle
- generated Rocq export

の drift を検出する。
こちらは semantic acceptance ではなく regression/reference check である。

## 現在の到達点

現在、この 2 CPU workload refinement path でできているのは次である。

- runtime が rows + lifecycle artifact を deterministic に emit する
- extracted Haskell checker がその artifact を受理/棄却できる
- QEMU fixture を regression reference として保持できる
- KVM でも smoke acceptance を回せる

## 現在の未達項目

まだ未達なのは次である。

- arbitrary number of jobs に自然に拡張できる generic family
- all Awkernel traces を含む workload family
- accepted workload trace からの generic candidate-source reuse
- dispatch-latency gap を吸収する scheduler-facing witness
- scheduler-relation
- bounded-delay / deadline proof

特に今の checker は `try_wakeup 1 .. 8` のような small finite range に依存して
おり、job 数が増えるとスケールしない。したがって次の task は、
job-id 固定の narrow checker から、有限 task 集合一般へ持ち上げる
adapter-local family の設計である。
