# Awkernel 2 CPUs Workload Refinement

このメモは、Awkernel の 2 CPU async/await workload trace を、RocqSched の
既存の operational boundary へつなぐときに、実際にどの順で何を行うかをまとめる
手順書である。ここで扱うのは common layer の拡張ではなく、Awkernel adapter layer と
concrete runtime layer の narrow な refinement 手順である。

この手順の目的は次である。

- Awkernel が emit した workload trace を serial log として取得する
- その log から sched_trace と task_trace block を取り出し、Haskell acceptance lane で
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
追加するのは Awkernel adapter-local checker と、runtime-local task_trace export
だけである。

## Acceptance artifacts: sched_trace と task_trace

current procedure が checker input として使う emitted artifact は 2 つある。

- `sched_trace`
  - block marker は `BEGIN_SCHED_TRACE ... END_SCHED_TRACE`
  - 各行は現在の adapter encoding では
    `cpu_id, event_tag, event_arg0, event_arg1, current, runnable_csv, need_resched, dispatch_target`
    の 8 列 TSV である
  - これは acceptance が読む scheduler-visible row stream であり、Rocq では
    `AwkernelSchedTraceEntry` に対応する
- `task_trace`
  - block marker は `BEGIN_TASK_TRACE ... END_TASK_TRACE`
  - 各行は現在の adapter encoding では `kind, subject, related`
    の 3 列 TSV である
  - `kind` は現在
    `Spawn`, `Runnable`, `Choose`, `Dispatch`, `Sleep`, `JoinWait`, `Complete`
    を取る
  - これは checker が root task、known-task set、join/completion dependency を
    要約するための task-family fact stream であり、Rocq では
    `AwkernelTaskTraceEntry` と `AwkernelTaskTraceSummary` に対応する

この 2 つは adapter-local emitted artifact であり、common layer に追加された API ではない。
acceptance lane は serial log からこれらを一時入力として抽出して読み、成功時に
repo 管理下の artifact として保存しない。

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
`baseline_trace::record_task_trace(...)` を呼ぶ形で記録される。workload trace 用 feature が
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

## Step 3: acceptance lane が log から sched_trace と task_trace block を抽出する

`check-workload-accept-*` は、生ログから

- `BEGIN_SCHED_TRACE ... END_SCHED_TRACE`
- `BEGIN_TASK_TRACE ... END_TASK_TRACE`

を抽出し、一時的な `sched_trace.tsv` と `task_trace.tsv` を作って Haskell runner に渡す。
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

Haskell 側では `sched_trace.tsv` と `task_trace.tsv` を読み、
まず extracted checker `awk_workload_accepts_sched_trace task_trace sched_trace`
で accepted workload family への membership を判定する。family を通った場合だけ、
`first_non_scheduler_relation_sched_trace_index task_trace sched_trace` で
full の `GlobalFIFO` scheduler-relation check を走らせる。relation mismatch が出た場合に限り、
`first_non_fifo_sched_trace_index sched_trace` で
trace-local な `GlobalFIFO` choose-order diagnostic を走らせる。
この Step が concrete trace analysis そのものであり、Rocq 側で実トレースを
個別に再検査しない。

## Step 5: acceptance outcome を観測する

この procedure の結果は `accept/reject + diagnostics` だけである。
成功時には exit code `0` と `accepted=true` の JSON payload を返し、失敗時には
固定した diagnostics schema と exit code class で constraint 種別と場所つきの
diagnostics を返す。
成功時に repo 管理下の artifact を追加出力しない。

現在の failure split は次である。

- sched_trace block が無い
- sched_trace block が空
- task_trace block が無い
- task_trace block が空
- sched_trace parse failure
- task_trace parse failure
- workload-family-rejection
- scheduler-relation-rejection
- global-fifo-rejection
- runner / checker module / runhaskell の起動失敗

negative tests は synthetic serial log を使ってこの diagnostics contract を固定する。
ここで固定するのは exact key set、stdout 上の単一 JSON payload、exit code class、
location field の presence rule である。したがって、failure は Haskell acceptance
lane と Python wrapper の境界で速く止まり、Rocq 側へ進まない。

## Acceptance Lane

この節では、Haskell checker が何を検査しているかを procedure から分離して記す。
current workflow では、concrete trace constraint の semantic oracle は
この acceptance lane である。

### Haskell checker が検査すること

acceptance lane は `sched_trace + task_trace` を入力に取り、少なくとも次を検査する。

- task_trace well-formedness  
  task_trace record 列そのものが、root task の導入、duplicate spawn の禁止、
  `JoinWait` の参照先の既知性などを満たして summary に畳み込めることを検査する。  
  Rocq では `task_trace_entry_valid`、`summarize_task_trace`、
  `task_trace_well_formed` がこの責務を定義し、全体の theorem surface では
  `accepted_workload_sched_trace_family` と
  `awk_workload_accepts_sched_trace_sound` / `awk_workload_accepts_sched_trace_complete`
  がその判定機の意味を固定する。
- finite-task family membership  
  checker が固定 job-id ではなく、task_trace から復元した有限 task 集合
  `atts_known_tasks` の上で sched_trace を読むことを意味する。  
  Rocq では `AwkernelTaskTraceSummary`、`task_trace_entry_step`、
  `summarize_task_trace` が task universe を構成し、
  `accepted_workload_sched_trace_family` が「その finite-task family に属する」
  という Prop-level 境界を与える。
- sched_trace/task_trace consistency  
  sched_trace 側の wakeup / choose / dispatch / complete が、
  task_trace から得た known task 集合、completion dependency、
  selected/dispatched/completed state と矛盾しないことを検査する。  
  Rocq では `sched_trace_step_after_start`、`sched_trace_family_member`、
  `accepted_workload_sched_trace_family` がこの整合性を表し、bool 判定との対応は
  `awk_workload_accepts_sched_trace_sound` / `awk_workload_accepts_sched_trace_complete`
  が与える。
- optional stutter admissibility  
  scheduler-irrelevant step を全部許すのではなく、現在の narrow workload family で
  意味を壊さない stutter row だけを許す。  
  Rocq では `sched_trace_is_stutter` が許される row shape を定義し、
  `sched_trace_step_after_start` がその row を adapter-local に受理する。
- start/end condition  
  trace が root task の wakeup で始まり、最後に root task が completed 集合へ入る
  ことを要求する。  
  Rocq では開始条件を `sched_trace_step_start`、終了条件を `accept_sched_trace_from` が与え、
  それらを含んだ family 全体を `accepted_workload_sched_trace_family` と
  `awk_workload_accepts_sched_trace_sound` / `awk_workload_accepts_sched_trace_complete`
  が持ち上げる。
- full GlobalFIFO scheduler-relation check  
  accepted family を通った trace について、scheduler-facing な `GlobalFIFO`
  relation が emitted `sched_trace` から再構成した canonical witness に対して
  成り立つかを検査する。これは acceptance lane における primary な
  scheduler-policy check である。  
  Rocq では `workload_scheduler_relation_candidates`、
  `workload_scheduler_relation_choice`、
  `workload_scheduler_relation_schedule`、
  `workload_scheduler_relation_jobs`、
  `sched_trace_global_fifo_scheduler_relation_checkb`、
  `first_non_scheduler_relation_sched_trace_index` がこの判定機を定義し、
  `accepted_workload_global_fifo_scheduler_relation_family` と
  `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_sound` /
  `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_complete`
  が bool 判定と Prop-level family の対応を固定する。
- trace-local GlobalFIFO choose-order diagnostic  
  relation mismatch が出たときだけ、`EvChoose` row で選ばれた job が
  `sched_trace` から読んだ canonical FIFO order の先頭かどうかを再検査する。
  これは primary oracle ではなく、`scheduler-relation-rejection` を
  `global-fifo-rejection` に絞り込むための narrow diagnostic である。  
  Rocq では `sched_trace_fifo_candidates`、`sched_trace_fifo_head`、
  `sched_trace_global_fifo_rowb`、`sched_trace_global_fifo_checkb`、
  `first_non_fifo_sched_trace_index` がこの diagnostic checker を与え、
  `accepted_workload_global_fifo_sched_trace_family` と
  `awk_workload_accepts_global_fifo_sched_trace_sound` /
  `awk_workload_accepts_global_fifo_sched_trace_complete`
  がその bool/Prop 境界を固定する。

この checker は fixed job-id example に依存せず、task_trace summary が与える
known task 集合の上で sched_trace matching を行う。runnable list の順序自体は意味論に使わず、
membership だけを使う。

### task_trace 側で見る record kind

- `Spawn`
- `Runnable`
- `Choose`
- `Dispatch`
- `Sleep`
- `JoinWait`
- `Complete`

### sched_trace 側で見る pattern

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

workload acceptance 本体については、

- `accepted_workload_sched_trace_family`
- `awk_workload_accepts_sched_trace_sound`
- `awk_workload_accepts_sched_trace_complete`

が、現在の finite-task workload family に対する theorem surface である。
さらに concrete trace 上の scheduler-relation / FIFO check については、

- `accepted_workload_global_fifo_sched_trace_family`
- `awk_workload_accepts_global_fifo_sched_trace_sound`
- `awk_workload_accepts_global_fifo_sched_trace_complete`
- `accepted_workload_global_fifo_scheduler_relation_family`
- `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_sound`
- `awk_workload_accepts_global_fifo_scheduler_relation_sched_trace_complete`

が、accepted family の上に載る scheduler-facing `GlobalFIFO` relation と
trace-local FIFO diagnostic の theorem surface を与える。
candidate-table 側では、

- `candidate_table_matches_rows_sound`
- `candidate_table_matches_rows_complete`

が sched_trace-only local contract に対する theorem surface を与える。
candidate-source reuse 側では、

- `accepted_workload_candidate_source_family`
- `accepted_workload_candidate_source_sound`

が accepted family, candidate table, execution/sched_trace correspondence を
adapter-local `os_local_candidate_source_adapter_contract` へ持ち上げる theorem surface を与える。

この Rocq 側が現在保証する境界は次である。

- emitted sched_trace/task_trace が adapter-local generation rules に従うことを generic に述べられる
- acceptance decision procedure の成功と failure を generic に説明できる
- accepted workload family と candidate table から adapter-local candidate-source bridge を構成できる

この Rocq 側ではまだ次を保証しない。

- all valid runtime traces を checker が完全に受理すること
- scheduler-facing witness や scheduler-relation をこの family 全体で与えること

## 現在の到達点

現在、この 2 CPU workload refinement path でできているのは次である。

- runtime が sched_trace + task_trace artifact を含む serial log を deterministic に emit する
- extracted Haskell checker がその log 由来の artifact を受理/棄却できる
- KVM でも smoke acceptance を回せる

## この手順の現在の限界

この手順がまだ扱わないものは次である。

- all Awkernel traces を含む workload family
- dispatch-latency gap を吸収する scheduler-facing witness
- scheduler-relation
- bounded-delay / deadline proof

現在の checker は fixed job-id の例に依存せず、task_trace summary が与える
known task 集合の上で sched_trace matching を行う。この段階での主張は
`current task-trace grammar family が受理する任意の有限 task set` に限られ、
Awkernel が emit しうる全 trace の coverage を意味しない。

## After the Current Procedure

この節では、現在実際に回している procedure の後ろにある後続拡張だけを記録する。
ここから先は operational procedure ではなく、accepted family を次の refinement reuse へ
接続する段階である。

### Step 9: scheduler-facing witness

candidate-source reuse の後段として、dispatch-latency gap を吸収する adapter-local
scheduler-facing witness を proof-side bridge として追加した。current minimal
module は `GlobalFIFO` を target にし、

- `workload_scheduler_facing_execution_matches_sched_trace`
- `workload_global_fifo_table_witness`
- `accepted_workload_scheduler_facing_family`
- `accepted_workload_scheduler_facing_adapter_contract`

を導入している。ここでの witness は physical 2-CPU projected schedule そのものではなく、
accepted `sched_trace` から読む logical scheduler-facing row state を、
capacity 1 の logical worker schedule として解釈する narrow bridge である。
physical 2-CPU runtime のうち、CPU 0 は scheduler/interrupt CPU として残り、
`GlobalFIFO` relation は worker CPU 1 本分の single-CPU contract に落としている。
common operational interface は変更しない。

### Future Step 10: stronger scheduler-relation reuse

current proof-side witness は `GlobalFIFO` に対する adapter-local bridge までであり、
その先の stronger algorithm-facing reuse や `CandidateSourceSpec` を伴う packaging は
Future Step 10 に残る。したがって、この文書の Step 1 から Step 5 は current procedure、
Step 9 は current proof bridge、Future Step 10 以降はその先にある拡張である。
