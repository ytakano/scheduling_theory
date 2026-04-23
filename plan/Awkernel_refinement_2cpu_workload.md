# Awkernel 2 CPUs Workload Refinement

このメモは、Awkernel の 2 CPU async/await workload trace を、RocqSched の
既存の operational boundary へつなぐときに、実際にどの順で何を行うかをまとめる
手順書である。ここで扱うのは common layer の拡張ではなく、Awkernel adapter layer と
concrete runtime layer の narrow な refinement 手順である。

この手順の目的は次である。

- Awkernel が emit した workload trace を serial log として取得する
- その log から rows と lifecycle block を取り出し、Haskell acceptance lane で
  concrete trace constraint を判定する
- concrete trace checking と generic refinement obligation を分離した現行境界を記録する

この手順の範囲外にあるものは次である。

- all Awkernel traces の被覆
- IPI, timer interrupt, preemption, migration を含む一般 trace family
- scheduler-relation
- ideal scheduler policy との一致
- bounded-delay / deadline 保証

## Procedure Overview

この節の番号付き Step は、現在実際に回している operational procedure だけを書く。
終点は `accept/reject + diagnostics` であり、Haskell checker の検査内容や
Rocq の generic theorem は後ろの別節へ分ける。

保持する abstract interface は既存の operational common layer である。

- `OpState`
- `OpEvent`
- `OSProjection`
- `OSLabeledProjection`
- `OSLocalAdapterContract`

workload trace のために common layer へ新しい event や state field は追加しない。
追加するのは Awkernel adapter-local checker と、runtime-local lifecycle export
だけである。

## Step 1: runtime が workload serial log を出力する

まず runtime で、既存の baseline trace に加えて task lifecycle export を記録する。
この段階で差し込むのは、後段の acceptance lane が concrete trace analysis を行うために
必要な concrete event source だけである。現在の主な差し込み点は次である。

- task spawn
- task becomes runnable
- scheduler choose
- scheduler dispatch
- task sleep
- join wait
- task complete

これらは `awkernel_async_lib` の executor / task / sleep / join_handle 側から
`baseline_trace::record_lifecycle(...)` を呼ぶ形で記録される。workload trace 用 feature が
有効なときだけ有効になり、通常 runtime path には影響を与えない。

workload trace VM では root orchestrator task を起動し、
`arm_dump_on_complete(root_task_id)` によって root task の完了時に dump を
1 回だけ行う。したがって、この段階で得られるのは workload 全体が終了した時点の
serial log である。

現在の representative workload は 4 つである。

- `single_async_trace_vm`
- `nested_spawn_trace_vm`
- `multi_async_trace_vm`
- `sleep_wakeup_trace_vm`

これらは semantic family の定義ではなく、runtime artifact を出す representative examples である。

## Step 2: QEMU/KVM で workload log を取得する

次に QEMU または Linux KVM で representative workload を起動し、serial log を取得する。
current runtime capture path は `awkernel/Makefile` にある。

代表的な target は次である。

- `capture-workload-log-qemu-2cpu`
- `capture-workload-log-kvm-2cpu`
- `check-workload-accept-qemu-2cpu`
- `check-workload-accept-kvm-2cpu`

QEMU と KVM はどちらも acceptance backend であり、current workflow では
checked-in workload fixture を保持しない。

## Step 3: acceptance lane が log から rows と lifecycle block を抽出する

`check-workload-accept-*` は、生ログから

- `BEGIN_TRACE_ROWS ... END_TRACE_ROWS`
- `BEGIN_TASK_LIFECYCLE ... END_TASK_LIFECYCLE`

を抽出し、一時的な `rows.tsv` と `lifecycle.tsv` を作って Haskell runner に渡す。
この一時 TSV は acceptance lane の内部入力であり、成功時に repo 管理下の artifact として
保存しない。

## Step 4: acceptance lane が extracted Haskell checker を実行する

実際の concrete trace constraint 判定は Haskell acceptance lane が担う。active path は次である。

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

Haskell 側では `rows.tsv` と `lifecycle.tsv` を読み、
extracted checker `awk_workload_accepts_trace lifecycle rows` を呼ぶ。
この Step が concrete trace analysis そのものであり、Rocq 側で実トレースを
個別に再検査しない。

## Step 5: acceptance outcome を観測する

この procedure の結果は `accept/reject + diagnostics` だけである。
成功時には `accept` を返し、失敗時には constraint 種別と場所つきの diagnostics を返す。
成功時に repo 管理下の artifact を追加出力しない。

現在の failure split は次である。

- rows block が無い
- lifecycle block が無い
- rows parse failure
- lifecycle parse failure
- semantic rejection

## Acceptance Lane

この節では、Haskell checker が何を検査しているかを procedure から分離して記す。
current workflow では、concrete trace constraint の semantic oracle は
この acceptance lane である。

### Haskell checker が検査すること

acceptance lane は `rows + lifecycle` を入力に取り、少なくとも次を検査する。

- lifecycle well-formedness
- finite-task family membership
- rows/lifecycle consistency
- optional stutter admissibility
- start/end condition

この checker は fixed job-id example に依存せず、lifecycle summary が与える
known task 集合の上で row matching を行う。runnable list の順序自体は意味論に使わず、
membership だけを使う。

### lifecycle 側で見る record kind

- `Spawn`
- `Runnable`
- `Choose`
- `Dispatch`
- `Sleep`
- `JoinWait`
- `Complete`

### rows 側で見る pattern

- wakeup row
- choose row
- dispatch row
- complete row
- optional stutter row

現在の受理器は次を要求する。

- root task の wakeup から開始する
- known task 以外は choose / dispatch / complete できない
- duplicate spawn を許さない
- invalid join edge を許さない
- sleeping / join dependency に反する completion を許さない
- `cpu=1`, `current=None`, `need_resched=false`, `dispatch_target=None` の
  narrow shape に限って optional stutter を許す
- trace 末尾で root task が completed に入っている

## Rocq Proof Role

この節では、Rocq で Haskell checker の何を証明しているかだけを記す。
current workflow では Rocq は concrete trace を個別に再検査しない。

Rocq 側に残している主な役割は次である。

- workload acceptance semantics の定義
- candidate-table local contract の定義
- decision procedure に対する generic soundness theorem
- decision procedure に対する generic completeness theorem
- 後段の refinement obligation

現在の source of truth は次である。

- `Operational/Awkernel/Minimal/WorkloadAcceptance.v`
- `Operational/Awkernel/Minimal/WorkloadCandidateTable.v`
- `Operational/Awkernel/Minimal/WorkloadAcceptanceExtraction.v`

この Rocq 側が現在保証する境界は次である。

- emitted rows/lifecycle が adapter-local generation rules に従うことを generic に述べられる
- acceptance decision procedure の成功と failure を generic に説明できる

この Rocq 側ではまだ次を保証しない。

- all valid runtime traces を checker が完全に受理すること
- accepted trace から generic local adapter contract を end-to-end で作ること
- candidate-source や scheduler-relation をこの family 全体で与えること

## 現在の到達点

現在、この 2 CPU workload refinement path でできているのは次である。

- runtime が rows + lifecycle artifact を含む serial log を deterministic に emit する
- extracted Haskell checker がその log 由来の artifact を受理/棄却できる
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

## After the Current Procedure

この節では、現在実際に回している procedure の後ろにある後続拡張だけを記録する。
ここから先は operational procedure ではなく、accepted family を次の refinement reuse へ
接続する段階である。

### Future Step 8: generic local refinement obligations

Step 5 の bool-valued acceptance boundary の後段では、Rocq が concrete trace を
個別に再検査するのではなく、acceptance decision procedure に対する generic
soundness/completeness theorem と、その accepted family に対する generic local
refinement obligations を扱う。この step は adapter layer の内部にとどまり、
common layer の event/state interface は増やさない。

### Future Step 9: scheduler-facing witness

Future Step 8 の後段では、dispatch-latency gap を吸収する adapter-local
scheduler-facing witness を導入する。この witness の役割は、accepted family に
対する後段の proof obligation を与えることであり、common operational interface
自体を変更することではない。

### Future Step 10: scheduler-relation

scheduler-relation は、Future Step 9 のさらに後段で扱う。したがって、この文書の
Step 1 から Step 5 は現在の procedure、Future Step 8 以降はその先にある番号付き拡張である。
