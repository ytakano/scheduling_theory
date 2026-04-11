# LLF optimality (finite job set 版) に向けた次タスク plan

## Goal

有限 job 集合に対する LLF optimality 定理、すなわち最終的に

```coq
Theorem llf_optimality_on_finite_jobs : ...

を証明する。

現状、EDF/LLF の共通化はかなり完了しており、
	•	LLF.v に choose_llf, choose_llf_min_laxity, llf_bundle, llf_scheduler
	•	LLFLemmas.v に canonical predicate / prefix 安定性
	•	generic canonical bridge
	•	EDF 側の EDFLemmas.v / EDFTransform.v / EDFOptimality.v

が揃っている。

したがって、次の本命タスクは LLF の violation / repair / normalization 層を追加し、EDF optimality の骨格を LLF に移植することである。

⸻

全体方針

LLF optimality は EDF と同様、以下の 3 層で構成する。
	1.	LLFLemmas.v
	•	局所 violation を定義する
	•	canonical LLF step では violation が起きないことを示す
	•	非 canonical step から repair witness を抽出する
	2.	LLFTransform.v
	•	非 canonical step を swap により repair する
	•	tie case / strict lower-laxity case を処理する
	3.	LLFOptimality.v
	•	repair を反復して canonical LLF schedule に normalize する
	•	generic bridge を用いて scheduler_rel を得る
	•	llf_optimality_on_finite_jobs を閉じる

⸻

Phase 1: LLFLemmas.v に violation 層を追加する

目的

repair lemma の入口となる「時刻 t に LLF 違反が起きている」とは何かを、EDF 版と平行な形で固定する。

⸻

Task 1-1: priority 述語を定義する

追加する定義

Definition respects_llf_priority_at_on
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  forall j j',
    sched t 0 = Some j ->
    J j ->
    J j' ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j t <= laxity jobs 1 sched j' t)%Z.

意味

時刻 t に走っている j は、J 内の eligible jobs の中で最小 laxity を持つ。

⸻

Task 1-2: explicit candidate list 版 violation を定義する

追加する定義

Definition llf_violation_at_in
    (J : JobId -> Prop)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time)
    (candidates : list JobId) : Prop :=
  exists j j',
    sched t 0 = Some j /\
    J j /\
    In j' candidates /\
    J j' /\
    eligible jobs 1 sched j' t /\
    (laxity jobs 1 sched j' t < laxity jobs 1 sched j t)%Z.

意味

時刻 t に実行されている j より strict に小さい laxity を持つ eligible candidate j' が存在する。

⸻

Task 1-3: candidates_of 版 violation を定義する

追加する定義

Definition llf_violation_at_with
    (J : JobId -> Prop)
    (candidates_of : CandidateSource)
    (jobs : JobId -> Job)
    (sched : Schedule)
    (t : Time) : Prop :=
  llf_violation_at_in J jobs sched t (candidates_of jobs 1 sched t).


⸻

Task 1-4: canonical LLF step では strict lower-laxity job が存在しないことを示す

追加したい補題

Lemma matches_choose_llf_at_with_no_lower_laxity_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j j',
    matches_choose_llf_at_with jobs candidates_of sched t ->
    sched t 0 = Some j ->
    In j' (candidates_of jobs 1 sched t) ->
    eligible jobs 1 sched j' t ->
    (laxity jobs 1 sched j t <= laxity jobs 1 sched j' t)%Z.

証明の核
	•	matches_choose_llf_at_with を展開して choose_llf ... = Some j を得る
	•	choose_llf_min_laxity を適用する

⸻

Task 1-5: canonical choose 一致から LLF priority を導く

追加したい補題

Lemma matches_choose_llf_at_with_implies_respects_llf_priority_at_on :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_llf_at_with jobs candidates_of sched t ->
    respects_llf_priority_at_on J jobs sched t.

証明の核
	•	cand_spec から eligible job が candidate list に入ることを得る
	•	Task 1-4 を適用する

⸻

Task 1-6: canonical LLF step では finite violation が起きないことを示す

追加したい補題

Lemma matches_choose_llf_at_with_no_finite_violation :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t,
    matches_choose_llf_at_with jobs candidates_of sched t ->
    ~ llf_violation_at_with J candidates_of jobs sched t.

証明の核
	•	violation から strict < の witness を得る
	•	Task 1-4 から <= を得る
	•	矛盾

⸻

Task 1-7: 非 canonical step から repair 候補を抽出する

追加したい主補題

Lemma canonical_non_llf_step_has_other_min_or_better_eligible_job :
  forall J candidates_of
         (cand_spec : CandidateSourceSpec J candidates_of)
         jobs sched t j,
    valid_schedule jobs 1 sched ->
    sched t 0 = Some j ->
    J j ->
    ~ matches_choose_llf_at_with jobs candidates_of sched t ->
    exists j',
      In j' (candidates_of jobs 1 sched t) /\
      eligible jobs 1 sched j' t /\
      (laxity jobs 1 sched j' t <= laxity jobs 1 sched j t)%Z /\
      j' <> j /\
      choose_llf jobs 1 sched t (candidates_of jobs 1 sched t) = Some j'.

証明の核
	•	valid_schedule と sched t 0 = Some j から eligible j t
	•	cand_spec から j が candidate list に入る
	•	choose_llf_some_if_exists により Some j' を得る
	•	choose_llf_min_laxity で laxity j' <= laxity j
	•	~ matches_choose_llf_at_with から j' <> j

⸻

Phase 1 の完了条件

以下が LLFLemmas.v に揃っていること。
	•	respects_llf_priority_at_on
	•	llf_violation_at_in
	•	llf_violation_at_with
	•	matches_choose_llf_at_with_no_lower_laxity_eligible_job
	•	matches_choose_llf_at_with_implies_respects_llf_priority_at_on
	•	matches_choose_llf_at_with_no_finite_violation
	•	canonical_non_llf_step_has_other_min_or_better_eligible_job

⸻

Phase 2: LLFTransform.v を新設して repair 層を作る

目的

Task 1-7 で得た witness j' を用いて、非 canonical step を swap によって canonical に修復する。

⸻

Task 2-1: tie-only repair を先に通す

まず作るべき補題

Lemma repair_non_canonical_at_llf_tie :
  ...

対象
	•	choose_llf ... = Some j'
	•	sched t 0 = Some j
	•	laxity j' t = laxity j t
	•	j' は将来 t' で実行されている

目標

swap_at sched t t' によって
	•	validity preserved
	•	feasibility preserved
	•	agrees_before sched sched' t
	•	matches_choose_llf_at_with jobs candidates_of sched' t

を示す。

理由

tie case は strict case より簡単で、repair interface を先に固められる。

⸻

Task 2-2: strict lower-laxity repair を追加する

追加したい補題

Lemma repair_non_canonical_at_llf_strict :
  ...

対象
	•	choose_llf ... = Some j'
	•	sched t 0 = Some j
	•	(laxity j' t < laxity j t)%Z

証明の核

ScheduleFacts.v にある
	•	実行されれば laxity 保存
	•	実行されなければ laxity が 1 減る

を利用し、
	•	より小さい laxity の job を前倒ししても feasibility が壊れない
	•	swap 後も validity / single-CPU / J-only が保たれる

ことを示す。

⸻

Task 2-3: 統合 repair lemma を作る

追加したい補題

Lemma repair_non_canonical_at_llf :
  ...

結論

EDF 版の repair_non_canonical_at と同じインターフェースで、
	•	valid_schedule jobs 1 sched'
	•	feasible_schedule_on J jobs 1 sched'
	•	J-only preserved
	•	single_cpu_only preserved
	•	agrees_before sched sched' t
	•	matches_choose_llf_at_with jobs candidates_of sched' t

を返す。

⸻

Phase 2 の完了条件
	•	LLFTransform.v が新設されている
	•	tie case repair が通っている
	•	strict case repair が通っている
	•	repair_non_canonical_at_llf が完成している

⸻

Phase 3: LLFOptimality.v を新設して normalization を作る

目的

repair lemma を繰り返し適用し、feasible witness を horizon まで canonical LLF schedule に正規化する。

⸻

Task 3-1: repair が first non-canonical time を押し上げる補題を作る

追加したい補題

Lemma repair_pushes_first_violation_forward_llf :
  ...

証明の核
	•	agrees_before により t0 未満は変わらない
	•	t0 では repair により canonical になる
	•	したがって first violation 時刻は前進する

⸻

Task 3-2: bounded normalization を作る

追加したい補題

Lemma llf_normalize_up_to :
  ...

内容

時刻 H 未満の LLF violation を順に潰し、H 未満では canonical LLF に一致する schedule を得る。

⸻

Task 3-3: horizon まで canonical にする

追加したい補題

Lemma llf_normalize_to_canonical :
  ...

内容

deadline_horizon jobs enumJ 未満で canonical な feasible schedule を構成する。

⸻

Task 3-4: truncation 補題を追加する

必要に応じて追加する補題

Lemma trunc_sched_llf_canonical :
  ...

内容

canonical な schedule を horizon で trunc_sched しても、horizon 未満では canonical 性が保たれる。

⸻

Phase 3 の完了条件
	•	LLFOptimality.v が新設されている
	•	repair_pushes_first_violation_forward_llf
	•	llf_normalize_up_to
	•	llf_normalize_to_canonical
	•	必要なら trunc_sched_llf_canonical

が証明されている

⸻

Phase 4: 最終定理 llf_optimality_on_finite_jobs を閉じる

目的

generic canonical bridge を使って、canonical LLF schedule から scheduler_rel を得て、finite-job optimality を示す。

⸻

Task 4-1: feasible witness を single-CPU witness に制限する

EDF 版と同様に、
	•	feasible witness を取る
	•	mk_single_cpu
	•	必要なら J_restrict

を適用する。

⸻

Task 4-2: canonical LLF witness を作る

Phase 3 の llf_normalize_to_canonical を使って、
	•	horizon 未満で canonical
	•	feasible
	•	valid
	•	single-CPU-only
	•	J-only

を満たす schedule を構成する。

⸻

Task 4-3: horizon 以後を idle にする

必要なら trunc_sched を使って、
	•	forall t, H <= t -> sched t 0 = None

を満たす schedule に変換する。

⸻

Task 4-4: generic bridge を適用する

SchedulingAlgorithmCanonicalBridge.v の generic bridge を用いて

scheduler_rel (single_cpu_algorithm_schedule llf_generic_spec candidates_of) jobs 1 sched

を得る。

⸻

Task 4-5: 最終定理を示す

追加する定理

Theorem llf_optimality_on_finite_jobs :
  ...

証明の流れ
	1.	feasible witness を取る
	2.	single CPU へ制限
	3.	canonical LLF witness へ normalize
	4.	horizon 以後を idle 化
	5.	generic bridge を適用
	6.	schedulable_by_on ... を結論する

⸻

Phase 4 の完了条件
	•	llf_optimality_on_finite_jobs が通る
	•	EDF finite-job optimality と同型の statement / proof skeleton になっている

⸻

実行順

以下の順に実装する。
	1.	LLFLemmas.v
	•	Task 1-1 ～ 1-7 を追加
	2.	LLFTransform.v
	•	tie-only repair
	•	strict repair
	•	repair_non_canonical_at_llf
	3.	LLFOptimality.v
	•	repair_pushes_first_violation_forward_llf
	•	llf_normalize_up_to
	•	llf_normalize_to_canonical
	•	必要なら truncation 補題
	4.	最終定理
	•	llf_optimality_on_finite_jobs

⸻

直近の次の一手

いま最優先でやるべきタスクはこれ。

Next Task

LLFLemmas.v に以下を追加する。
	•	respects_llf_priority_at_on
	•	llf_violation_at_in
	•	llf_violation_at_with
	•	matches_choose_llf_at_with_no_lower_laxity_eligible_job
	•	matches_choose_llf_at_with_implies_respects_llf_priority_at_on
	•	matches_choose_llf_at_with_no_finite_violation
	•	canonical_non_llf_step_has_other_min_or_better_eligible_job

このタスクが完了すると、LLFTransform.v の statement がほぼ確定し、repair 層へ進める。

⸻

Notes
	•	LLF の難所は chooser ではなく repair である。
	•	共通化リファクタリングにより、prefix / canonical / bridge 層はかなり再利用可能になっている。
	•	したがって、実質的な新規証明コストは
	•	LLF violation extraction
	•	LLF swap repair
	•	LLF normalization
に集中している。
	•	最初の repair は tie-only case から始めるのが安全である。
