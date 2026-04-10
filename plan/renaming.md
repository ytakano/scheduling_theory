
目的

現状の
	•	DispatchInterface
	•	DispatchSchedulerBridge
	•	DispatcherRefinement
	•	SchedulerValidity

を中心とした構成を、
	•	SchedulingAlgorithm
	•	Scheduler
	•	Schedule

の三層へ再整理する。

特に、
	•	旧 Dispatcher / DispatchSpec は SchedulingAlgorithm
	•	旧 DispatchPolicy は SchedulingAlgorithmSpec あるいは AlgorithmPolicy
	•	旧 dispatcher_refines_policy は algorithm_refines_spec
	•	Scheduler は引き続き上位の relation / semantic package

として整理する。

⸻

命名方針

残すもの
	•	Schedule
	•	Scheduler

置き換えるもの
	•	Dispatcher → SchedulingAlgorithm
	•	GenericDispatchSpec → GenericSchedulingAlgorithm
	•	DispatchPolicy → SchedulingAlgorithmSpec
	•	dispatcher_refines_policy → algorithm_refines_spec
	•	DispatchSchedulerBridge → SchedulingAlgorithmSchedulerBridge
	•	DispatchInterface → SchedulingAlgorithmInterface
	•	DispatchLemmas → SchedulingAlgorithmLemmas
	•	DispatchClassicalLemmas → SchedulingAlgorithmClassicalLemmas
	•	DispatcherRefinement → SchedulingAlgorithmRefinement

⸻

中核概念の意味づけ

1. Schedule

実行結果そのもの。

(* A schedule is the execution timeline:
   for each time t and CPU c, it returns the job running there, if any. *)

2. SchedulingAlgorithm

単一時刻において、候補から何を選ぶかを決める executable なアルゴリズム。

(* A scheduling algorithm is an executable local decision procedure:
   given the current context and candidate jobs, it selects the next job
   to run, if any. *)

3. Scheduler

SchedulingAlgorithm を、候補集合生成・妥当性条件・CPU構成・refinement などと合わせて、
「どの schedule がこの方式で生成されるか」を表す上位仕様。

(* A scheduler is a semantic scheduling object:
   it characterizes which schedules are admitted for a given job set
   and machine size, typically by combining a scheduling algorithm with
   candidate generation, validity conditions, and refinement obligations. *)


⸻

修正 plan

Phase 1: 用語だけ先に揃える

まず record 名・ファイル名・コメントを揃えます。
この段階では意味を変えず、名前だけ変えるのが重要です。

変更対象
	•	DispatchInterface.v
	•	DispatchSchedulerBridge.v
	•	DispatcherRefinement.v
	•	DispatchLemmas.v
	•	DispatchClassicalLemmas.v
	•	UniSchedulerInterface.v
	•	roadmap.md
	•	README.md

この段階でやること
	1.	Dispatch を SchedulingAlgorithm に置換
	2.	DispatchPolicy を SchedulingAlgorithmSpec に置換
	3.	コメント中の “dispatcher” を “scheduling algorithm” に修正
	4.	Scheduler は「algorithm + constraints + semantics」の説明に修正

⸻

Phase 2: SchedulingAlgorithm の基底 interface を作る

旧 DispatchInterface.v を改名し、ここに SchedulingAlgorithm の executable interface を置きます。

新ファイル名
	•	SchedulingAlgorithmInterface.v

ここに置く定義
	•	旧 GenericDispatchSpec を改名した record
	•	select_job あるいは run_algorithm 的な field
	•	選択結果の基本健全性

推奨定義

Record GenericSchedulingAlgorithm : Type := mkGenericSchedulingAlgorithm {
  run_algorithm :
    (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId ;

  algorithm_eligible :
    forall jobs m sched t candidates j,
      run_algorithm jobs m sched t candidates = Some j ->
      eligible jobs m sched j t ;

  algorithm_some_if_eligible_candidate :
    forall jobs m sched t candidates,
      (exists j, In j candidates /\ eligible jobs m sched j t) ->
      exists j', run_algorithm jobs m sched t candidates = Some j' ;

  algorithm_none_if_no_eligible_candidate :
    forall jobs m sched t candidates,
      (forall j, In j candidates -> ~ eligible jobs m sched j t) ->
      run_algorithm jobs m sched t candidates = None ;

  algorithm_in_candidates :
    forall jobs m sched t candidates j,
      run_algorithm jobs m sched t candidates = Some j ->
      In j candidates
}.

ポイント
	•	field 名 dispatch を残すより、run_algorithm か choose_job の方が新命名と整合的
	•	ただし既存コードの churn を抑えるなら、field 名だけ dispatch のまま残してもよい
その場合 record 名だけ先に変える

私のおすすめは、
	•	record 名は変える
	•	field 名は最初は残す
です。
一気に field 名まで変えると修正量が増えやすいです。

⸻

Phase 3: SchedulingAlgorithmSpec を切り出す

旧 SchedulerValidity.v の DispatchPolicy は、実質
「このアルゴリズムの出力として許されるもの」を定める述語です。

これは SchedulingAlgorithmSpec と呼ぶのが自然です。

新ファイル名候補
	•	SchedulingAlgorithmSpec.v

ただしファイル数を増やしたくないなら、
	•	SchedulerValidity.v を維持しつつ中の定義名だけ改名
でもよいです。

推奨定義

Definition SchedulingAlgorithmSpec :=
  (JobId -> Job) -> nat -> Schedule -> Time -> list JobId -> option JobId -> Prop.

旧名からの置換
	•	DispatchPolicy → SchedulingAlgorithmSpec
	•	PolicySanity → SchedulingAlgorithmSpecSanity
	•	respects_policy_at → respects_algorithm_spec_at
	•	respects_policy_at_with → respects_algorithm_spec_at_with
	•	respects_policy_before → respects_algorithm_spec_before

コメント方針

ここでは「これは executable algorithm そのものではなく、algorithm が満たすべき specification」であることを明記する。

⸻

Phase 4: bridge を SchedulingAlgorithmSchedulerBridge に改名

旧 DispatchSchedulerBridge.v は、
SchedulingAlgorithm を Scheduler に持ち上げる橋なので、ここが一番名前と意味の対応が良くなります。

新ファイル名
	•	SchedulingAlgorithmSchedulerBridge.v

ここに置くもの
	•	CandidateSource
	•	CandidateSourceSpec
	•	single_cpu_algorithm_schedule
	•	single_cpu_algorithm_valid
	•	single_cpu_algorithm_scheduler_on

旧名からの対応
	•	single_cpu_dispatch_schedule
→ single_cpu_algorithm_schedule
	•	single_cpu_dispatch_valid
→ single_cpu_algorithm_valid
	•	single_cpu_dispatch_scheduler_on
→ single_cpu_algorithm_scheduler_on

代表定義

Definition single_cpu_algorithm_schedule
    (alg : GenericSchedulingAlgorithm)
    (candidates_of : CandidateSource)
    : Scheduler :=
  mkScheduler (fun jobs m sched =>
    m = 1 /\
    forall t,
      sched t 0 = alg.(run_algorithm) jobs 1 sched t (candidates_of jobs 1 sched t) /\
      forall c, 0 < c -> sched t c = None).


⸻

Phase 5: refinement を改名

旧 DispatcherRefinement.v は名前の変更だけでかなり意味が明瞭になります。

新ファイル名
	•	SchedulingAlgorithmRefinement.v

新定義名

Definition algorithm_refines_spec
    (alg : GenericSchedulingAlgorithm)
    (spec : SchedulingAlgorithmSpec) : Prop :=
  forall jobs m sched t candidates,
    spec jobs m sched t candidates
      (alg.(run_algorithm) jobs m sched t candidates).

旧名からの対応
	•	dispatcher_refines_policy
→ algorithm_refines_spec

⸻

Phase 6: UniSchedulerBundle を SchedulingAlgorithm 前提で整理

旧 UniSchedulerInterface.v はかなり重要です。
ここは
	•	concrete algorithm
	•	abstract algorithm spec
	•	candidate source
	•	refinement
	•	scheduler 化

をまとめる場所なので、名前を揃えるだけで意味が見えやすくなります。

置換
	•	HasGenericDispatchSpec
→ HasGenericSchedulingAlgorithm
	•	to_generic_dispatch_spec
→ to_generic_scheduling_algorithm
	•	usb_policy
→ usb_alg_spec
	•	usb_policy_sane
→ usb_alg_spec_sane
	•	usb_refines
→ usb_algorithm_refines

record 名

UniSchedulerBundle はそのままでよいです。
なぜならこれは “algorithm + constraints + semantics” を束ねた Scheduler 側の bundle だからです。

推奨コメント

(* UniSchedulerBundle packages the ingredients needed to build a verified
   single-CPU scheduler from:
   - a concrete scheduling algorithm,
   - an abstract algorithm specification,
   - a candidate-source discipline,
   - and a refinement proof connecting them. *)


⸻

Phase 7: Schedule / SchedulingAlgorithm / Scheduler の定義を明示的にファイルへ書く

これは重要です。
今のコードベースでは意味が複数ファイルに散っているので、概念定義を1箇所にまとめるファイルを作るのがおすすめです。

新規追加ファイル
	•	SchedulingConcepts.v

このファイルに書く内容
	1.	Schedule の意味
	2.	SchedulingAlgorithm の意味
	3.	Scheduler の意味
	4.	三者の関係
	5.	今後の拡張方針

具体案

From Stdlib Require Import Arith.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.

(* ====================================================== *)
(* Core scheduling concepts used throughout the project.  *)
(* ====================================================== *)

(* Schedule:
   the execution timeline produced by a scheduler. *)
(* Schedule itself is defined in ScheduleModel.v. *)

(* SchedulingAlgorithm:
   an executable local decision procedure that selects the next job
   from a candidate set at each time step. *)
(* GenericSchedulingAlgorithm is defined in SchedulingAlgorithmInterface.v. *)

(* Scheduler:
   a semantic object characterizing which schedules are admitted for
   a given job set and machine size.  A scheduler typically combines
   a scheduling algorithm with candidate generation, validity conditions,
   and refinement obligations. *)
(* Scheduler is defined in SchedulerInterface.v. *)

(* Intended layering:
   Schedule              = result
   SchedulingAlgorithm   = local executable choice rule
   Scheduler             = global semantic/constraint wrapper *)

このファイルを作る理由
	•	README に説明を書くより、コード中で一貫した語彙を固定できる
	•	AIエージェントや将来の自分が「このプロジェクトの基本用語」を参照しやすい
	•	コメントの散逸を防げる

⸻

定義をどのファイルに書くべきか

1. Schedule

置き場所
	•	既存の ScheduleModel.v に残す
	•	ただし概念説明は SchedulingConcepts.v にも書く

理由

Schedule はすでに周辺定義
	•	eligible
	•	valid_schedule
	•	service
などと密接なので、モデル定義ファイルから動かさない方がよいです。

⸻

2. SchedulingAlgorithm

置き場所
	•	SchedulingAlgorithmInterface.v

理由

これは executable algorithm の基底抽象なので、interface ファイルに置くのが自然です。

⸻

3. Scheduler

置き場所
	•	既存の SchedulerInterface.v に残す
	•	ただしコメントを更新する

推奨コメントへの差し替え

(* A scheduler is a semantic scheduling abstraction.
   It characterizes which schedules are admitted for a given job set
   and machine size, typically by combining a scheduling algorithm with
   additional constraints and semantic obligations. *)


⸻

実際の rename 一覧

ファイル
	•	DispatchInterface.v
→ SchedulingAlgorithmInterface.v
	•	DispatchSchedulerBridge.v
→ SchedulingAlgorithmSchedulerBridge.v
	•	DispatcherRefinement.v
→ SchedulingAlgorithmRefinement.v
	•	DispatchLemmas.v
→ SchedulingAlgorithmLemmas.v
	•	DispatchClassicalLemmas.v
→ SchedulingAlgorithmClassicalLemmas.v

record / class / definition
	•	GenericDispatchSpec
→ GenericSchedulingAlgorithm
	•	HasGenericDispatchSpec
→ HasGenericSchedulingAlgorithm
	•	to_generic_dispatch_spec
→ to_generic_scheduling_algorithm
	•	DispatchPolicy
→ SchedulingAlgorithmSpec
	•	PolicySanity
→ SchedulingAlgorithmSpecSanity
	•	dispatcher_refines_policy
→ algorithm_refines_spec

bridge 関数
	•	single_cpu_dispatch_schedule
→ single_cpu_algorithm_schedule
	•	single_cpu_dispatch_valid
→ single_cpu_algorithm_valid
	•	single_cpu_dispatch_scheduler_on
→ single_cpu_algorithm_scheduler_on

validity / respect
	•	respects_policy_at
→ respects_algorithm_spec_at
	•	respects_policy_at_with
→ respects_algorithm_spec_at_with
	•	respects_policy_before
→ respects_algorithm_spec_before
	•	single_cpu_policy_schedule
→ single_cpu_algorithm_spec_schedule
	•	single_cpu_policy_scheduler
→ single_cpu_algorithm_spec_scheduler

⸻

実装順のおすすめ

Step 1

まず SchedulingConcepts.v を追加して、
Schedule / SchedulingAlgorithm / Scheduler の意味をコメントで固定する。

Step 2

DispatchInterface.v を SchedulingAlgorithmInterface.v に改名し、
GenericDispatchSpec を GenericSchedulingAlgorithm に改名する。
この段階では field 名は据え置きでもよい。

Step 3

DispatchSchedulerBridge.v を改名し、関数名を ...algorithm... に置換する。

Step 4

DispatcherRefinement.v と SchedulerValidity.v の用語を揃える。

Step 5

UniSchedulerInterface.v の bundle 内フィールド名を揃える。

Step 6

README.md と roadmap.md の
	•	chooser
	•	dispatch
	•	dispatcher
	•	policy
の説明を新用語へ更新する。

⸻

roadmap / README に書くべき短い説明

以下をそのまま使えます。

- Schedule: 実行結果そのもの。時刻とCPUに対して、どの job が走るかを表す。
- SchedulingAlgorithm: 各時刻で候補集合から次に実行する job を選ぶ局所的・実行可能なアルゴリズム。
- Scheduler: SchedulingAlgorithm を、候補生成、妥当性条件、CPU 構成、refinement などと合わせて schedule semantics に持ち上げた全体仕様。


⸻

最終的な設計の見え方

最終形は、概念的にこうなります。

Schedule
  = 実行結果

SchedulingAlgorithm
  = 局所的な選択アルゴリズム

SchedulingAlgorithmSpec
  = そのアルゴリズムが満たすべき抽象仕様

Scheduler
  = SchedulingAlgorithm
    + CandidateSource
    + Validity / Sanity
    + Refinement
    + CPU / machine structure
    + Schedule semantics

この分け方だと、
	•	EDF / FIFO / RR は SchedulingAlgorithm
	•	それらの order 性質や tie 性質は SchedulingAlgorithmSpec
	•	schedulable_by などは Scheduler

に自然に載ります。
