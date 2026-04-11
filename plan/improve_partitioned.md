
目的

Partitioned.v にある
	•	raw_partitioned_schedule_on（内部の dispatch equation）
	•	valid_partitioned_schedule（公開 API）

の境界を、コメントだけでなく実際の定義でも成立させる。

具体的には、valid_partitioned_schedule を単なる alias から卒業させ、
partitioned scheduler の公開仕様として使える形に強化する。
そのうえで、PartitionedCompose.v と PartitionedPolicies/* をその新しい公開仕様に追従させる。

⸻

変更対象ファイル

優先順は次の通りです。
	1.	theories/Partitioned.v
	2.	theories/PartitionedCompose.v
	3.	theories/PartitionedPolicies/PartitionedEDF.v
	4.	theories/PartitionedPolicies/PartitionedFIFO.v
	5.	theories/PartitionedPolicies/PartitionedRR.v
	6.	theories/PartitionedPolicies/PartitionedLLF.v
	7.	theories/SchedulableExamples.v

⸻

フェーズ1: Partitioned.v の公開仕様を実体化する

1-1. valid_partitioned_schedule を強化する

現状は:

Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
  raw_partitioned_schedule_on jobs sched.

これを、まずは次に変更する。

第1段階の推奨形

Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
  raw_partitioned_schedule_on jobs sched /\
  respects_assignment sched.

将来の最終形候補

Definition valid_partitioned_schedule (jobs : JobId -> Job) (sched : Schedule) : Prop :=
  raw_partitioned_schedule_on jobs sched /\
  respects_assignment sched /\
  valid_schedule jobs m sched.

ただし、最初から valid_schedule まで入れると既存補題の修正が広がるので、
まずは 2 項版で入れるのが安全です。

⸻

1-2. intro/elimination 補題を作り直す

追加・修正する補題

Partitioned.v に次を追加する。

Lemma valid_partitioned_schedule_intro :
  forall jobs sched,
    raw_partitioned_schedule_on jobs sched ->
    respects_assignment sched ->
    valid_partitioned_schedule jobs sched.

Lemma valid_partitioned_schedule_raw :
  forall jobs sched,
    valid_partitioned_schedule jobs sched ->
    raw_partitioned_schedule_on jobs sched.

Lemma valid_partitioned_schedule_respects_assignment :
  forall jobs sched,
    valid_partitioned_schedule jobs sched ->
    respects_assignment sched.

もし第2段階で valid_schedule も入れたら、さらに

Lemma valid_partitioned_schedule_valid :
  forall jobs sched,
    valid_partitioned_schedule jobs sched ->
    valid_schedule jobs m sched.

も追加する。

⸻

1-3. 既存定理の仮定を整理する

現状、以下の定理は valid_partitioned_schedule を受けていますが、
中で alias として扱っています。
	•	assignment_respect
	•	partitioned_schedule_implies_valid_schedule
	•	local_valid_feasible_on_implies_global
	•	partitioned_schedulable_by_on_from_local

これらを、新しい valid_partitioned_schedule に合わせて書き直す。

修正方針

assignment_respect
現状は partitioned_schedule_implies_respects_assignment に渡しているが、
今後は直接

apply valid_partitioned_schedule_respects_assignment in Hvps.

の形に寄せる。

partitioned_schedule_implies_valid_schedule
内部で必要なのは raw_partitioned_schedule_on なので、

pose proof (valid_partitioned_schedule_raw _ _ Hvps) as Hraw.
pose proof (valid_partitioned_schedule_respects_assignment _ _ Hvps) as Hresp.

という形に変更する。

local_valid_feasible_on_implies_global
これも同様に、Hvps から Hresp を公開補題で取り出す。

⸻

1-4. 名前の整理

現状の valid_partitioned_schedule_elim は、定義強化後には意味が弱すぎます。
以下のように整理したほうがよいです。
	•	valid_partitioned_schedule_elim は削除または deprecated comment
	•	代わりに
	•	valid_partitioned_schedule_raw
	•	valid_partitioned_schedule_respects_assignment
	•	必要なら valid_partitioned_schedule_valid

を正式 API にする

⸻

フェーズ2: partitioned_schedulable_by_on_from_local を公開仕様ベースに揃える

この補題は、今後の partitioned の 標準入口なので、最重要です。

2-1. 仮定の意味を明確にする

現状の statement はすでに良いですが、
valid_partitioned_schedule が強化されることで、意味が実体化されます。

Lemma partitioned_schedulable_by_on_from_local :
  ...
  valid_partitioned_schedule n spec cands jobs sched ->
  (forall c, c < n ->
    feasible_schedule_on (local_jobset assign J c) jobs 1 (cpu_schedule sched c)) ->
  schedulable_by_on J (partitioned_scheduler n spec cands) jobs n.

これは今後も維持する。

⸻

2-2. proof を public API 経由に変更する

proof 内で
	•	partitioned_schedule_implies_valid_schedule
	•	partitioned_schedule_implies_respects_assignment

を直接使っているので、
新しい valid_partitioned_schedule_* 射影補題に寄せた形にする。

特に proof の読みやすさのため、

pose proof (valid_partitioned_schedule_respects_assignment _ _ Hvps) as Hresp.

を最初に置く形にするのがよいです。

⸻

フェーズ3: PartitionedCompose.v を新 API に追従させる

PartitionedCompose.v は glue 層です。
ここでは内部 theorem は raw のままでもよいですが、
公開入口では valid を返す形に寄せるのがよいです。

3-1. raw theorem は残してよい

現状の

Theorem glue_local_rels_imply_partitioned_schedule_on :
  ...
  raw_partitioned_schedule_on m spec cands jobs
    (glue_local_schedules m locals).

は内部補題として有用なので残す。

ただし名前は少し見直してもよいです。

候補:
	•	glue_local_rels_imply_raw_partitioned_schedule_on

⸻

3-2. valid 版の theorem を追加する

次を追加するのが自然です。

Theorem glue_local_rels_imply_valid_partitioned_schedule :
  forall m spec (cands : CPU -> CandidateSource)
         jobs (locals : CPU -> Schedule),
    (forall c, c < m ->
      scheduler_rel
        (single_cpu_algorithm_schedule spec (cands c))
        jobs 1 (locals c)) ->
    respects_assignment ... ->   (* 必要ならここで導く *)
    valid_partitioned_schedule m spec cands jobs
      (glue_local_schedules m locals).

ただし respects_assignment は glue の形から直接示す必要があるので、
ここで新補題を一つ足すのがよいです。

⸻

3-3. glue_local_schedules 用の assignment respect 補題を追加する

新規補題候補:

Lemma glue_local_schedules_respects_assignment :
  forall assign m (locals : CPU -> Schedule),
    (forall j, assign j < m) ->
    ...

ただし今の PartitionedCompose.v は assign を theorem に渡していないので、
ここでは無理に一般化せず、local_witnesses_imply_partitioned_schedulable_by_on の中で
valid_partitioned_schedule_intro に必要な respects_assignment を
別補題で供給する形でもよいです。

より現実的には、次の補題を足すのがよいです。

Lemma glue_local_schedules_respects_assignment_from_cands :
  ...

ただ、ここは少し設計の自由度があります。
最小修正で行くなら、Partitioned.v 側の既存定理

partitioned_schedule_implies_respects_assignment

を raw から導いて、その結果を valid_partitioned_schedule_intro に渡せば十分です。

つまり PartitionedCompose.v では、まず raw を出し、次にそれから respects を出して valid を組む。

⸻

3-4. local_witnesses_imply_partitioned_schedulable_by_on を修正する

現状:

apply valid_partitioned_schedule_intro.
apply glue_local_rels_imply_partitioned_schedule_on.
...

これを次の形に変える。

apply valid_partitioned_schedule_intro.
- apply glue_local_rels_imply_partitioned_schedule_on.
  ...
- apply partitioned_schedule_implies_respects_assignment.
  apply glue_local_rels_imply_partitioned_schedule_on.
  ...

ただし raw の証明を二度書くのは冗長なので、

pose proof (glue_local_rels_imply_partitioned_schedule_on ...) as Hraw.
apply valid_partitioned_schedule_intro.
- exact Hraw.
- apply partitioned_schedule_implies_respects_assignment with ...; exact Hraw.

のように共有するのがよいです。

⸻

フェーズ4: PartitionedPolicies/* を thin wrapper として揃える

対象:
	•	PartitionedEDF.v
	•	PartitionedFIFO.v
	•	PartitionedRR.v
	•	PartitionedLLF.v

4-1. 各 wrapper でやること

各ファイルでやることは同じです。
	•	scheduler 定義はそのまま
	•	local witness → global schedulable_by_on theorem は維持
	•	proof は local_witnesses_imply_partitioned_schedulable_by_on に完全委譲

この意味で、これらのファイルは さらに薄くできる 可能性があります。

⸻

4-2. 各ファイルで確認する補題

PartitionedEDF.v
	•	local_edf_witnesses_imply_partitioned_edf_schedulable_by_on

PartitionedFIFO.v
	•	FIFO 版対応 theorem

PartitionedRR.v
	•	RR 版対応 theorem

PartitionedLLF.v
	•	LLF 版対応 theorem

ここで見るべき点は、各 theorem の proof が
	•	generic theorem に完全委譲できているか
	•	ローカル固有の変換が最小限か

です。

⸻

フェーズ5: SchedulableExamples.v を public predicate ベースに直す

ここは実用上かなり重要です。
example が新 API の使用例になるからです。

5-1. 修正対象

grep で見えている箇所では、少なくとも
	•	valid_partitioned_schedule 2 fifo_generic_spec pair_cands pair_jobs pair_sched
	•	apply valid_partitioned_schedule_intro
	•	unfold raw_partitioned_schedule_on
	•	apply (partitioned_schedulable_by_on_intro ...)

の周辺を見直す必要があります。

⸻

5-2. 修正方針

変更前の典型
	•	valid_partitioned_schedule_intro に raw だけ渡している
	•	proof 中で raw_partitioned_schedule_on を直接展開している

変更後
	•	valid_partitioned_schedule_intro に
	•	raw
	•	respects_assignment
を両方渡す
	•	できれば example 側では raw_partitioned_schedule_on の unfold を減らす
	•	可能なら partitioned_schedulable_by_on_from_local を使って example を書き換える

つまり、example も「公開入口の使い方」を示すように寄せる。

⸻

フェーズ6: コメントと抽象境界を実装に一致させる

Partitioned.v のコメントにはすでに
	•	raw は internal
	•	valid は public API
	•	将来 strengthen する

という方針が書かれています。

これを実装に合わせて更新します。

6-1. 更新するコメント

valid_partitioned_schedule の説明

現状は「今は alias」と書いてあるので、変更後は
	•	raw dispatch equation
	•	assignment respect
	•	将来的には global validity も含めうる

という説明に直す。

partitioned_schedulable_by_on_from_local の説明

「3-step entry point」であることは非常に良いので、そのまま残す。
ただし Step 1 の意味を
	•	valid_partitioned_schedule を示す
	•	それにより internal equation + assignment respect を得る

と少し具体化するとよいです。

⸻

補題レベルの作業リスト

Partitioned.v

追加・修正する補題一覧:
	•	valid_partitioned_schedule_intro 修正
	•	valid_partitioned_schedule_raw 追加
	•	valid_partitioned_schedule_respects_assignment 追加
	•	assignment_respect 修正
	•	partitioned_schedule_implies_valid_schedule 修正
	•	local_valid_feasible_on_implies_global 修正
	•	partitioned_schedulable_by_on_from_local proof 修正

必要なら将来:
	•	valid_partitioned_schedule_valid 追加

⸻

PartitionedCompose.v

追加・修正する補題一覧:
	•	glue_local_rels_imply_partitioned_schedule_on は維持
	•	必要なら rename:
	•	glue_local_rels_imply_raw_partitioned_schedule_on
	•	local_witnesses_imply_partitioned_schedulable_by_on 修正
	•	Hraw を先に立てる
	•	Hraw から respects_assignment を導く
	•	valid_partitioned_schedule_intro に両方渡す

⸻

PartitionedPolicies/*.v

確認・必要なら修正:
	•	EDF/FIFO/RR/LLF 各 theorem が generic lifting theorem に薄く委譲されていること
	•	raw predicate へ依存していないこと

⸻

SchedulableExamples.v

修正:
	•	valid_partitioned_schedule_intro の適用箇所
	•	raw_partitioned_schedule_on を直接 unfold している箇所
	•	可能なら partitioned_schedulable_by_on_from_local を使った形へ寄せる

⸻

実施順

おすすめの実施順はこれです。

Step A

Partitioned.v で valid_partitioned_schedule を 2 項版に変更

Step B

valid_partitioned_schedule_* 射影補題を追加

Step C

Partitioned.v 内の既存 theorem を追従

Step D

PartitionedCompose.v の local_witnesses_imply_partitioned_schedulable_by_on を修正

Step E

PartitionedPolicies/* を確認・追従

Step F

SchedulableExamples.v を public API ベースに修正

Step G

コメント更新

⸻

完了条件

この plan の完了条件は次です。
	•	valid_partitioned_schedule が alias ではない
	•	public theorem 群が valid_partitioned_schedule を本当に公開仕様として使っている
	•	PartitionedCompose.v が新しい public predicate を構成できる
	•	policy wrapper がそのまま使える
	•	example が新 API の正しい使い方を示している

⸻

次の一手としての評価

このタスクは、単に名前を整えるだけではありません。
partitioned 層の抽象境界を本当に固定する作業です。

これを先にやると、その後の
	•	partitioned scheduler の追加
	•	multicore 共通性質
	•	global/clustered への拡張
	•	OS operational semantics への接続

がかなりやりやすくなります。
