次タスク plan: Round Robin を導入する

目的

現在の実装は
	•	共通基盤
	•	単一CPU抽象
	•	FIFO / EDF の concrete chooser
	•	abstract policy
	•	refinement
	•	partitioned composition
	•	partitioned EDF

まで揃っています。

したがって次は、履歴依存の policy でもこの抽象が十分かを確認するために、Round Robin を 1 本通すのが最も良いです。

FIFO/EDF は「候補列の先頭から選ぶ」「最小 deadline を選ぶ」という比較的静的な policy ですが、RR は
	•	候補列の回転
	•	現在時刻・直前の選択結果への依存
	•	queue 順序の更新

を扱う必要があります。
ここを通せれば、今の設計が prefix-dependent policy にも耐えることを実証できます。

⸻

実装方針

重要なのは、今の抽象を壊さずに RR を載せることです。

そのために、
	•	choose_rr 自体は「その時点の candidate list から 1 job を選ぶ」関数として定義し
	•	candidate の生成側で RR 順序を表現する

という分担にします。

つまり、RR の “状態” を chooser の内部に持ち込むのではなく、
	•	CandidateSource
	•	CandidateSourceSpec

を通して、時刻 t と schedule prefix を見て、RR 順序に並んだ candidate list を返す

ようにします。

これは Partitioned.v の設計意図とも一致しています。

⸻

Phase 1. 単一CPU RR policy の最小核を作る

1-1. 新規ファイル作成

追加候補:
	•	theories/UniPolicies/RoundRobin.v

ここにまず RR の最小実装を入れます。

⸻

1-2. まずは「chooser」を最小にする

RR では、candidate list 自体が「今この時点の RR 順序」を表しているとみなし、
chooser は FIFO と同じく
	•	候補列を先頭から走査
	•	最初の eligible job を返す

でよいです。

つまり実装上は、最初の段階では
	•	chooser の挙動は FIFO と同型
	•	意味づけだけが RR

になります。

これは不自然ではありません。
RR の本質は「どの job が先頭に来る candidate list を作るか」にあるためです。

この段階で入れるもの
	•	choose_rr
	•	choose_rr_eligible
	•	choose_rr_some_if_exists
	•	choose_rr_none_if_no_eligible
	•	choose_rr_in_candidates

実際には FIFO の補題をかなり再利用できるはずです。
必要なら FIFO の chooser 補題を generic lemma に抽出してもよいですが、まずは duplication を許して前進して構いません。

⸻

1-3. rr_generic_spec を作る

FIFO.v と同様に、
	•	rr_generic_spec : GenericSchedulingAlgorithm

を定義します。

これで bridge 側はそのまま再利用できます。

⸻

Phase 2. abstract RR policy を定義する

2-1. RR policy の表現を明確化する

ここで重要なのは、RR を何として定義するかです。

このプロジェクトの現状では、最も自然なのは次です。

「candidate list は現在の RR queue 順序を表し、
scheduler はその中の最初の eligible job を選ぶ」

この形なら、policy は FIFO policy とほぼ同じ形になります。

具体的には
	•	None のとき: candidate に eligible job がない
	•	Some j のとき:
	•	candidates = prefix ++ j :: suffix
	•	j は eligible
	•	prefix 内の job はすべて ineligible

となります。

見た目は FIFO と同じですが、candidate list の意味が FIFO と RR で異なるのが重要です。

FIFO:
	•	candidate list = 到着順 queue

RR:
	•	candidate list = 現時点の rotation 後 queue

⸻

2-2. rr_policy / sanity / refinement

RoundRobin.v に次を入れます。
	•	rr_policy : SchedulingAlgorithmSpec
	•	rr_policy_sane : SchedulingAlgorithmSpecSanity rr_policy
	•	choose_rr_refines_rr_policy : algorithm_refines_spec rr_generic_spec rr_policy

この時点で、単一CPUの verified bundle を組めます。

⸻

2-3. bundle と scheduler wrapper

FIFO.v と同じパターンで、
	•	rr_bundle
	•	rr_scheduler_on
	•	rr_policy_scheduler_on

を定義します。

ここまでで、RR が UniSchedulerBundle にきちんと載ります。

⸻

Phase 3. RR 用 CandidateSource の意味を明文化する

ここが RR で一番重要です。

3-1. コメントで明示すべきこと

CandidateSource は単なる候補集合列挙ではなく、RR では
	•	queue 順序
	•	回転済み順序
	•	quantum 切れ後の requeue 後順序

を表すものとして使う、と明記した方がよいです。

特に RoundRobin.v の冒頭コメントで、
	•	chooser は queue を更新しない
	•	queue の更新結果は candidates_of jobs 1 sched t に織り込まれる
	•	よって RR の operational 部分は candidate source 側の責務

と書いておくと、後続の prioritized FIFO や OS semantics に繋がりやすいです。

⸻

3-2. 今回は quantum をどう扱うか

最初の RR 導入では、量子長 q = 1 の RR から始めるのがよいです。

理由:
	•	離散時刻モデルと相性が良い
	•	毎 tick ごとに queue rotation を candidate source 側で表せる
	•	先に抽象を通せる

その後、必要なら
	•	quantum : nat
	•	連続実行カウント
	•	quantum 消費後の rotation

に一般化できます。

したがって、今回の次タスクでは unit-quantum RR を明示して始めるのが安全です。

⸻

Phase 4. 小さい例を追加する

4-1. example ファイル

追加候補:
	•	theories/RRExamples.v
または
	•	theories/SchedulableExamples.v に追記

まずは小さい例で十分です。

例の内容
	•	2〜3 job
	•	単一CPU
	•	candidates_of が RR 順序を返す
	•	rr_scheduler_on を満たす schedule の witness
	•	可能なら schedulable_by_on の簡単な導出

この段階では、大きい theorem は不要です。
目的は interface に実際に載っていることの確認です。

⸻

Phase 5. partitioned RR を追加する

5-1. 新規ファイル

追加候補:
	•	theories/PartitionedPolicies/PartitionedRR.v

内容は PartitionedPolicies/PartitionedEDF.v と同じく、薄い wrapper で十分です。

⸻

5-2. 入れる定義と定理
	•	partitioned_rr_scheduler
	•	local_rr_witnesses_imply_partitioned_rr_schedulable_by_on

定理の形は EDF 版と揃えます。

つまり、
	•	各 CPU ごとに rr_scheduler_on を満たす local schedule があり
	•	各 local schedule が local feasible

なら、
	•	global に schedulable_by_on J (partitioned_rr_scheduler ...) jobs m

を得る形です。

⸻

Phase 6. ここまで終わったら次に prioritized FIFO

RR の次は prioritized FIFO が自然です。

順番として RR を先に置く理由は、
	•	FIFO/EDF では見えない履歴依存性を試せる
	•	candidate source の expressive power を検証できる

からです。

その上で prioritized FIFO に進めば、
	•	priority 順
	•	同 priority 内 FIFO
	•	tie-case の policy 表現

を今の SchedulingAlgorithmSpec でどう書くかを整理できます。

⸻

具体的ファイル単位 plan

追加するファイル
	•	theories/UniPolicies/RoundRobin.v
	•	theories/PartitionedPolicies/PartitionedRR.v
	•	theories/RRExamples.v もしくは SchedulableExamples.v への追記

⸻

UniPolicies/RoundRobin.v に入れる順序
	1.	choose_rr
	2.	generic lemmas
	•	chosen job is eligible
	•	exists eligible -> returns Some
	•	none -> no eligible
	•	chosen job in candidates
	3.	rr_generic_spec
	4.	rr_policy
	5.	rr_policy_sane
	6.	choose_rr_refines_rr_policy
	7.	rr_bundle
	8.	rr_scheduler_on
	9.	rr_policy_scheduler_on

⸻

PartitionedPolicies/PartitionedRR.v に入れる順序
	1.	import 群
	2.	partitioned_rr_scheduler
	3.	local_rr_witnesses_imply_partitioned_rr_schedulable_by_on

⸻

examples に入れるもの
	1.	小さい jobs 定義
	2.	小さい RR candidate source
	3.	local witness schedule
	4.	rr_scheduler_on の確認
	5.	可能なら partitioned 2CPU の小例

⸻

この plan で注意する点

1. RR の「本体」は chooser ではなく candidate source 側

これを曖昧にすると、後で
	•	queue state を chooser が持つのか
	•	schedule prefix が queue state を決めるのか

が混乱します。

今回の設計では後者です。

⸻

2. まずは q=1 で固定する

いきなり一般 quantum を入れると、
	•	連続実行長
	•	current job 継続条件
	•	quantum 残量

まで必要になり、設計が一段重くなります。

まずは 1 tick RR を通すのがよいです。

⸻

3. FIFO と実装が似ていても問題ない

初期段階では
	•	chooser のコードは FIFO と同型
	•	semantics は candidate source の意味づけで差が出る

という形で十分です。

これはむしろ、今の抽象化が正しい方向である証拠です。

⸻

仕上がりの到達点

この次タスクが終わった時点で、プロジェクトは
	•	EDF
	•	FIFO
	•	RR
	•	partitioned EDF
	•	partitioned RR

を同じ抽象基盤で扱えるようになります。

これにより、
	•	単一CPU policy family の拡充
	•	partitioned lifting の一般性の確認
	•	prioritized FIFO / global policy / OS semantics への足場

が揃います。

