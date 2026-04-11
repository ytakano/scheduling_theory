確認できた範囲では、次にやるべきタスクは partitioned scheduling の合成性を、抽象インターフェース込みで 1 本通すこと です。理由は、更新後ロードマップが明確に「共通基盤 → 単一CPU理論 → partitioned / global / clustered」と積み上げる形を採っており、その中でも partitioned は「単一CPU理論の再利用がしやすい最初のマルチコア到達点」とされているからです。特に、Phase 7.1 で assign : JobId -> CPU、CPU ごとの valid schedule、全体 schedule への合成、service/completion の持ち上げが次の具体項目として挙がっており、Phase 9.1 でも最初に狙うべき schedulability とされています。 ￼  ￼

また、実装側はすでにこの段階へ進むだけの下地があります。Task/Job/Schedule、service、released、pending、ready、valid_schedule、feasible、schedulable、さらに有限・部分集合向けの feasible_on / schedulable_on まで入っており、multicore 側の基本不変条件として no_duplication 相当もあります。したがって、今は新しい policy を増やすより、単一CPUの理論を partitioned に持ち上げる bridge 層を固めるのが最も自然です。 ￼  ￼

次タスクの主目標

主目標は次の 3 つです。
	1.	partitioned schedule の定義を固定する
「job は割当先 CPU 以外では走らない」を明示した global schedule の妥当性述語を作ることです。これは roadmap の 7.1 と Lv.5 の「per-CPU valid から global valid」に対応します。 ￼  ￼
	2.	service 分解補題を証明する
partitioned では各 job の service は割当先 CPU だけから来る、という補題を入れます。これは後で feasible / schedulable を持ち上げるときの中核になります。 ￼
	3.	per-CPU 性質を global 性質へ持ち上げる
valid、feasible_on、必要なら schedulable_on を、CPU ごとの仮定から全体へ持ち上げます。これは roadmap の「各 CPU が valid なら全体も valid」「各 CPU が feasible なら全体も feasible」に対応します。 ￼

具体 plan

Step 1: Partitioned 用の基礎定義を 1 ファイルに分離する

まず Partitioned.v か PartitionedScheduler.v を作り、次を置きます。
	•	assign : JobId -> CPU
	•	runs_only_on_assigned_cpu
	•	cpu_schedule または project_cpu_schedule
	•	valid_partitioned_schedule

ここで valid_partitioned_schedule は、少なくとも次を含む形がよいです。
	•	global valid_schedule jobs m sched
	•	割当尊重: sched t c = Some j -> assign j = c
	•	必要なら c < m 範囲でのみ議論

概念的にはこうです。

Definition respects_assignment
    (assign : JobId -> CPU) (m : nat) (sched : Schedule) : Prop :=
  forall t c j, c < m -> sched t c = Some j -> assign j = c.

Definition valid_partitioned_schedule
    (assign : JobId -> CPU)
    (jobs : JobId -> Job)
    (m : nat)
    (sched : Schedule) : Prop :=
  valid_schedule jobs m sched /\
  respects_assignment assign m sched.

この段階では、以前話していた「全部入り述語」にしてもよいですが、最初は valid_schedule と assignment respect を分けておいた方が補題が書きやすいです。

Step 2: CPU 射影を定義する

各 CPU の単一CPU view を formalize します。

Definition cpu_schedule (sched : Schedule) (c : CPU) : Schedule :=
  fun t cpu' => if Nat.eqb cpu' 0 then sched t c else None.

あるいは、単一CPU用に型を分けているなら

Definition cpu_schedule1 (sched : Schedule) (c : CPU) : Time -> option JobId :=
  fun t => sched t c.

の方が後の補題はかなり素直です。もし uniprocessor 側 interface がすでにあるなら、multicore の Schedule を無理に再利用するより、射影先は単一CPU schedule 型に落とす方がよいです。

Step 3: service 分解補題を最優先で入れる

最初の山はこれです。
	•	assigned_cpu_only_runs_job
	•	cpu_count_non_assigned_zero
	•	partitioned_service_eq_assigned_cpu_service

狙う定理の形は例えば次です。

Lemma cpu_count_zero_on_unassigned_cpu :
  forall assign jobs sched m j t c,
    valid_partitioned_schedule assign jobs m sched ->
    c < m ->
    assign j <> c ->
    sched t c <> Some j.

Lemma partitioned_service_localizes :
  forall assign jobs sched m j t,
    valid_partitioned_schedule assign jobs m sched ->
    service m sched j t =
    service 1 (cpu_schedule sched (assign j)) j t.

これは roadmap の Lv.5「partitioned では job の service は割当先 CPU 上の service と一致」「他 CPU の寄与は 0」にそのまま対応します。 ￼

Step 4: valid の持ち上げ補題を書く

次に、

Lemma per_cpu_valid_implies_global_valid : ...

を証明します。ただし実際には「各 CPU の local valid」だけだと足りず、assignment respect が必要です。したがって構成は
	•	local 側: 割当先 CPU の schedule は valid
	•	global 側: それを束ねた schedule は valid_partitioned_schedule

という向きにするとよいです。

ここで「他 CPU に勝手に現れない」が効くので、先に Step 3 をやるのが重要です。

Step 5: feasible_on の持ち上げを入れる

finite/対象集合向けに既に feasible_on / schedulable_on があるので、ここを使うのが一番きれいです。 ￼

狙う定理は次です。

Lemma per_cpu_feasible_on_implies_partitioned_feasible_on :
  forall assign J jobs m sched,
    valid_partitioned_schedule assign jobs m sched ->
    (forall c, c < m ->
       feasible_on (fun j => J j /\ assign j = c) jobs 1 (cpu_schedule sched c)) ->
    feasible_on J jobs m sched.

これで roadmap の「各 CPU が feasible なら全体も feasible」が一段具体化できます。 ￼

Step 6: 最後に scheduler 抽象へ接続する

ここで初めて partitioned_scheduler を作ります。構成としては
	•	単一CPU scheduler interface
	•	assign
	•	per-CPU scheduler instances
	•	それらを束ねる PartitionedScheduler

です。

この層では、以前の議論どおり SchedulingAlgorithm と Scheduler を分けるのが自然です。
つまり、
	•	SchedulingAlgorithm: ready/current/state から選択を返すもの
	•	Scheduler: algorithm + validity/refinement/feasibility 仮定を含む仕様パッケージ

としておくと、partitioned は「各 CPU に algorithm を載せた scheduler」の合成として書けます。

ファイル案

今の流れなら、次の分け方が扱いやすいです。
	•	Base.v
既存の Job, Task, Schedule, service, valid_schedule, feasible_on など。これは現状維持でよいです。 ￼  ￼
	•	Partitioned.v
assign, respects_assignment, cpu_schedule, valid_partitioned_schedule
	•	PartitionedLemmas.v
service 分解、valid 持ち上げ、feasible 持ち上げ
	•	PartitionedScheduler.v
単一CPU scheduler を per-CPU に lift する構成
	•	必要なら PartitionedSchedulability.v
per-CPU EDF / FIFO / prioritized FIFO を束ねる定理

この順にする理由

この順にすると、global scheduling や laxity-based scheduler へ進む前に、multicore 最初の成功例が手に入ります。更新ロードマップでも partitioned は global より先で、しかも理論的に「かなり現実的な到達点」と位置付けられています。逆にここを飛ばして global work-conserving や top-m selection へ行くと、carry-in や interference の前に基礎の合成則が不足したままになります。 ￼  ￼

今すぐ着手するなら最初の 3 タスク

最初のコミット単位まで落とすと、次です。
	1.	Partitioned.v を作り、respects_assignment と valid_partitioned_schedule を定義する。
	2.	PartitionedLemmas.v を作り、cpu_count_zero_on_unassigned_cpu と partitioned_service_localizes を証明する。
	3.	per_cpu_feasible_on_implies_partitioned_feasible_on を証明し、partitioned bridge を完成させる。
