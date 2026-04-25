# Periodic EDF verified checker proof plan

## 0. Goal

周期タスク集合を CSV から受け取り、Haskell 側で生成した certificate を
extracted Rocq checker で検査し、checker が `true` を返したら、Rocq 側で
無限時間の periodic EDF schedulability を結論できる形まで閉じる。

最終的な目標形は次。

```coq
Theorem check_periodic_edf_csv_certificate_sound :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    schedulable_by_on
      (periodic_jobset
        (extracted_task_scope ts)
        (extracted_periodic_tasks ts)
        (fun _ => 0)
        (extracted_periodic_jobs ts))
      (edf_scheduler
         (periodic_candidates_before
            (extracted_task_scope ts)
            (extracted_periodic_tasks ts)
            (fun _ => 0)
            (extracted_periodic_jobs ts)
            (enumT_of_extracted_list ts)
            (extracted_periodic_codec ts)))
      (extracted_periodic_jobs ts)
      1.
```

この theorem では、certificate generator は trusted にしない。信頼境界は
Rocq で証明された boolean checker とその soundness theorem だけに置く。

## 1. Current proof frontier

すでに存在する主要な境界は次。

- finite DBF / classical DBF checker は extracted task set から計算できる。
- prefix certificate は semantic checker と generated EDF prefix との一致 checker を持つ。
- representative backlog-free prefix は `check_transport_classes_rep_backlog_generated`
  で検査できる。
- residue coverage / residue shift は `check_periodic_transport_residue_coverage` と
  `check_transport_residue_shifts` で検査できる。
- window transport target / pair completeness は
  `check_window_transport_targets_complete_with_pairs` で検査できる。
- post-reset bounded target coverage は
  `check_post_reset_window_targets_complete_with_pairs` と
  `check_post_reset_target_list_complete` で有限 candidate list に落ちている。
- hyperperiod state reset は `check_periodic_hyperperiod_state_reset` で検査できる。
- arbitrary job と bounded representative pair の関係を拾う checker として
  `check_hyperperiod_block_source_pair_in_certs` が追加済み。

現時点の final theorem 群には、互換性のため次を Prop obligation として受け取る
legacy variant が残っている。

- `TransportClassRepresentativeObligation`
- `PeriodicHyperperiodBlockServiceSourceObligation`
- `PeriodicHyperperiodServicePairTransportObligation`
- `PeriodicHyperperiodBoundaryResetCompletionObligation`
- またはそれらをまとめる `PeriodicHyperperiodGeneratedSchedulePeriodicity`

一方で、実装済みの generated representative 経路では
`TransportClassRepresentativeObligation` は外部仮定から消えている。
当初 mainline は
`check_periodic_edf_checked_sidecar_extracted_checked_block_generated_rep_sound`
を使う予定だったが、checked block-source normalization は
finite certificate 内の concrete delta と arbitrary job の hyperperiod delta を
一致させる必要があり、無限時刻の arbitrary jobs には過剰に強い。

以後の mainline は、bounded `target0/x0` の certificate membership は checker から得て、
arbitrary `target/x` との shift delta は canonical periodic semantics から Prop として
構成する。つまり final assembly では checked block-source normalization ではなく、
`PeriodicHyperperiodBlockServiceSourceObligation` を extracted/canonical theorem で閉じる
generated representative variant を使う。

mainline に残る Prop obligation は次。

- `PeriodicHyperperiodServicePairTransportObligation`
- `PeriodicHyperperiodBoundaryResetCompletionObligation`

`PeriodicHyperperiodBlockServiceSourceObligation` は
`check_periodic_edf_checked_sidecar_extracted_block_service_source_obligation`
で checker と canonical periodic semantics から構成済み。

次の作業は、これらを checker と canonical periodic semantics から構成して、
extraction-facing soundness theorem の仮定から消すこと。

## 2. Semantic assumptions

最終 checker soundness で固定する semantic assumptions は、extracted CSV 入力に
対応する canonical periodic model に限定する。

- task id は `enumT_of_extracted_list ts = seq 0 (length ts)` で列挙される。
- offset は常に `fun _ => 0`。
- jobs は `extracted_periodic_jobs ts`、つまり
  `canonical_periodic_jobs_from_enumT` で生成される。
- `extracted_taskset_wf ts = true` から、各 in-scope task の period/cost/deadline は正。
- hyperperiod は `periodic_hyperperiod_positive` で正。
- in-scope task の period は `periodic_hyperperiod_divides` で hyperperiod を割る。
- canonical jobs では同一 task の jobs の cost は task WCET と一致する。

generic `generated_by_periodic_task` は `job_cost <= task_cost` しか持たない。
そのため、cost equality が必要な arbitrary-job transport は generic theorem ではなく、
まず extracted/canonical jobs 用 theorem として閉じる。

## 3. Required observable events

新しい runtime observable event は不要。

checker が見るべき情報は certificate と task/job parameters のみ。

- prefix slots
- transport basis jobs
- transport class id / shift
- representative jobs
- window target certificates
- window pair certificates
- post-reset target certificates
- hyperperiod reset boundary
- release/deadline/cost equality for shifted pairs

Rust scheduler や OS trace から追加で観測すべき event はない。Rust 側が担当するのは
certificate generation であり、soundness は extracted checker が担う。

## 4. Interface delta

### 4.1 Checked block-source normalization

まず `PeriodicEDFTransportWitnessChecker.v` に checker-based normalization record を置く。

```coq
Record PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs)
    (target_certs : list EDFWindowTransportTargetCert) : Prop := {
  periodic_hyperperiod_checked_block_source_normalization :
    forall target x,
      periodic_jobset T tasks offset jobs target ->
      periodic_jobset_deadline_between
        T tasks offset jobs 0 (job_abs_deadline (jobs target)) x ->
      job_release (jobs x) < job_release (jobs target) ->
      job_release (jobs target) < periodic_hyperperiod tasks enumT \/
      periodic_hyperperiod tasks enumT <= job_release (jobs x) ->
      (exists boundary delta,
        periodic_hyperperiod tasks enumT <= boundary /\
        (exists n, delta = periodic_hyperperiod tasks enumT * n) /\
        boundary = periodic_hyperperiod tasks enumT + delta /\
        boundary <= job_release (jobs target) /\
        job_release (jobs x) < boundary)
      \/
      exists target0 x0,
        periodic_jobset T tasks offset jobs target0 /\
        job_release (jobs target0) <
          post_reset_target_candidate_horizon tasks enumT /\
        periodic_jobset_deadline_between
          T tasks offset jobs 0 (job_abs_deadline (jobs target0)) x0 /\
        job_release (jobs x0) < job_release (jobs target0) /\
        check_hyperperiod_block_source_pair_in_certs
          tasks enumT jobs target x target0 x0 target_certs = true
}.
```

この record は `PeriodicHyperperiodBlockServiceSourceObligation` より checker 寄りで、
target certificate membership や pair membership を Prop として手で渡さない。

### 4.2 Checked normalization soundness

次を証明する。

```coq
Lemma periodic_hyperperiod_block_service_source_of_checked_normalization :
  PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
    T tasks offset jobs enumT codec target_certs ->
  PeriodicHyperperiodBlockServiceSourceObligation
    T tasks offset jobs enumT codec target_certs.
```

pair case は `check_hyperperiod_block_source_pair_in_certs_sound` で閉じる。
reset case は `periodic_hyperperiod_block_service_source_reset` を直接使う。

### 4.3 Extracted canonical normalization

次に extracted/canonical jobs 専用の constructor theorem を置く。

```coq
Theorem extracted_periodic_checked_block_source_normalization :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    PeriodicHyperperiodCheckedBlockSourceNormalizationObligation
      (extracted_task_scope ts)
      (extracted_periodic_tasks ts)
      (fun _ => 0)
      (extracted_periodic_jobs ts)
      (enumT_of_extracted_list ts)
      (extracted_periodic_codec ts)
      sidecar.(checked_post_reset_window_target_certs).
```

この theorem の中で arbitrary `target/x` を bounded `target0/x0` に正規化する。

## 5. Proof obligations

### Phase A: checker-to-Prop bridge

目的:
`check_hyperperiod_block_source_pair_in_certs` を
`PeriodicHyperperiodBlockServiceSourceObligation` に接続する。

Status: Done.

実装順:

1. `PeriodicHyperperiodCheckedBlockSourceNormalizationObligation` を追加。
2. `periodic_hyperperiod_block_service_source_of_checked_normalization` を証明。
3. final theorem variant を追加し、`PeriodicHyperperiodBlockServiceSourceObligation`
   の代わりに checked normalization obligation を受け取る。

期待される結果:
block-source の certificate membership は checker から復元される。

### Phase B: bounded representative construction

目的:
arbitrary `target/x` を bounded `target0/x0` に戻す。

基本方針:

1. `hp := periodic_hyperperiod tasks enumT` と置く。
2. reset-covered case は、ある hyperperiod boundary `boundary` が
   `job_release x < boundary <= job_release target` を満たす場合に選ぶ。
3. それ以外では `target` と `x` は同じ hyperperiod block にあるので、
   同じ `delta = hp * n` だけ戻して bounded window の `target0/x0` を作る。
4. `target0` は release が
   `post_reset_target_candidate_horizon = 2 * hp + max_deadline`
   未満になるように選ぶ。
5. `x0` は `target0` と同じ delta で戻す。

必要補題:

```coq
Lemma hyperperiod_block_no_boundary_same_delta :
  job_release x < job_release target ->
  ~(exists boundary, hp <= boundary /\
     (exists n, boundary = hp + hp * n) /\
     job_release x < boundary <= job_release target) ->
  exists n,
    hp * n <= job_release x /\
    job_release target < hp * S n.
```

```coq
Lemma canonical_job_shift_back_by_hyperperiod :
  periodic_jobset extracted ... target ->
  hp * n <= job_release target ->
  exists target0,
    periodic_jobset extracted ... target0 /\
    job_release target = job_release target0 + hp * n /\
    job_abs_deadline target = job_abs_deadline target0 + hp * n /\
    job_cost target = job_cost target0.
```

同じ lemma を `x` にも使う。

注意:
generic `PeriodicCodec` だけでは job id を明示構成しにくい。
extracted/canonical jobs では `encode_job_id_from_enumT` と
`decode_job_id_from_enumT` を使えるため、ここで閉じる。

Status:
`hyperperiod_block_no_boundary_same_delta`、
`extracted_periodic_shift_back_job_by_hyperperiod`、
`extracted_periodic_shift_back_deadline_between_pair` を追加済み。
これにより no-boundary same-block case では、bounded `target0/x0`、
post-reset horizon、deadline-between、release order、
`HyperperiodShiftedServicePair` まで構成できる。
残る作業は、この bounded pair を既存 post-reset certificate coverage と
`check_hyperperiod_block_source_pair_in_certs` に接続すること。

### Phase C: bounded pair coverage by existing post-reset checkers

目的:
構成した `target0/x0` が certificate に入っていることを既存 checker から得る。

使うもの:

- `check_post_reset_target_list_complete`
- `check_post_reset_window_targets_complete_with_pairs`
- `bounded_post_reset_window_target_list_coverage_of_checked_candidates`
- `bounded_post_reset_window_target_basis_coverage_of_checked_targets`
- `post_reset_window_target_coverage_of_checked_basis`
- `check_window_generated_pair_semantics_all_sound`

追加する theorem:

```coq
Lemma checked_post_reset_bounded_pair_coverage :
  check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
  periodic_jobset ... target0 ->
  job_release (jobs target0) < post_reset_target_candidate_horizon ... ->
  periodic_jobset_deadline_between ... target0 x0 ->
  job_release (jobs x0) < job_release (jobs target0) ->
  exists target_cert p,
    In target_cert sidecar.(checked_post_reset_window_target_certs) /\
    target_cert.(window_transport_target_job) = target0 /\
    In p target_cert.(window_transport_pairs) /\
    p.(window_target_earlier_job) = x0.
```

最終的にはこの theorem を boolean checker 版へ寄せる。
`check_hyperperiod_block_source_pair_in_certs` が `true` であることを直接示せるなら、
membership theorem は補助に下げる。

Status:
membership と `HyperperiodShiftedServicePair` から
`check_hyperperiod_block_source_pair_in_certs = true` を構成する
checker completeness bridge は追加済みだが、これは finite concrete witness 用の補助に下げる。

bounded `target0/x0` と certificate membership は既存
`BoundedPostResetWindowTargetCoverageObligation` から構成できる。
arbitrary `target/x` から bounded `target0/x0` への hyperperiod delta は
certificate から復元せず、`extracted_periodic_shift_back_deadline_between_pair`
で canonical semantics から構成する。

計画修正:
最終 normalization は
`PeriodicHyperperiodCheckedBlockSourceNormalizationObligation` ではなく
`PeriodicHyperperiodBlockServiceSourceObligation` を直接構成する。
理由は、checked normalization record が `p.(window_transport_delta)` と
arbitrary job の hyperperiod delta の一致を要求するため、有限 certificate では
無限時刻の arbitrary jobs を自然に覆えないからである。

### Phase D: shifted service pair construction

目的:
`target/x` と `target0/x0` の release/deadline/cost shift を boolean checker で示す。

既存 checker:

- `check_hyperperiod_delta_multiple`
- `check_hyperperiod_shifted_service_pair`
- `check_hyperperiod_block_source_pair_in_certs`

必要補題:

```coq
Lemma canonical_hyperperiod_shifted_service_pair_check :
  canonical_shift_relation target x target0 x0 delta ->
  check_hyperperiod_shifted_service_pair
    tasks enumT jobs target x target0 x0 delta = true.
```

ここで cost equality は canonical jobs に限定して証明する。

Status:
`HyperperiodShiftedServicePair` から
`check_hyperperiod_shifted_service_pair = true` を構成する generic completeness
lemma は追加済み。canonical jobs 側に残る作業は
`HyperperiodShiftedServicePair` そのものの構成。
その後、canonical job の exact cost と、
codec transport relation から `HyperperiodShiftedServicePair` を構成する
extracted 専用 bridge も追加済み。
arbitrary `target/x` から、この bridge に渡せる bounded `target0/x0` と
index shift relation を構成する補題も追加済み。
`BoundedPostResetWindowTargetCoverageObligation` の membership と組み合わせて
`PeriodicHyperperiodBlockServiceSourceObligation` にする theorem は追加済み。

### Phase E: schedule-level periodic transport

目的:
`PeriodicHyperperiodServicePairTransportObligation` と
`PeriodicHyperperiodBoundaryResetCompletionObligation` を消す。

既存の bridge:

- `periodic_hyperperiod_service_pair_transport_of_periodicity`
- `periodic_hyperperiod_boundary_reset_completion_of_periodicity`

次の方針で閉じる。

優先案:
`PeriodicHyperperiodGeneratedSchedulePeriodicity` を generated EDF schedule の
periodicity theorem から証明する。

補助入力:
state-reset checker と pair-completion checker は、それぞれ first-boundary reset
completion と bounded representative pair の source service completion を与える。
ただし、これらだけでは arbitrary target への transport は閉じない。
target 側の completion を得るには、generated EDF schedule の hyperperiod shift
invariance が必要である。

優先案の理由:
schedule-level periodicity は checker ではなく semantic theorem として一度閉じた方が、
certificate size を増やさず、Rust 側 observable も増やさない。

必要補題:

```coq
Theorem generated_periodic_edf_schedule_hyperperiodic :
  extracted_taskset_wf ts = true ->
  PeriodicHyperperiodGeneratedSchedulePeriodicity
    (extracted_task_scope ts)
    (extracted_periodic_tasks ts)
    (fun _ => 0)
    (extracted_periodic_jobs ts)
    (enumT_of_extracted_list ts)
    (extracted_periodic_codec ts).
```

この theorem は最も重い。閉じにくい場合は、まず boundary reset と service shift を
別 theorem に分ける。

計画修正:
`extracted_periodic_shift_forward_candidate_before` は shifted job が shifted finite
candidate enumeration に入ること、つまり membership だけを示す。
しかし `choose_edf` は `choose_min_metric` 経由で同一 deadline の tie-break を
candidate list の順序に依存して解く。したがって、schedule-level periodicity を
証明するには、candidate set の membership 対応だけでは不十分である。

次は、generated EDF の 1 step を運ぶために、次の順序で補題を足す。

1. canonical extracted jobs について、`enum_periodic_jobs_before` の hyperperiod
   shift が task order と job-index order を保つことを示す。
2. shifted prefix schedules が対応している仮定の下で、release / completed /
   eligible / metric が hyperperiod shift で保存されることを示す。
3. filtered eligible candidate list の order-preserving shift を示す。
4. `choose_edf` の結果が shifted job へ写ることを示す。
5. その 1 step 補題を induction で
   `generated_periodic_edf_schedule_upto` の prefix shift theorem に持ち上げる。
6. prefix shift theorem から
   `PeriodicHyperperiodServicePairTransportObligation` と
   `PeriodicHyperperiodBoundaryResetCompletionObligation` を構成する。

この修正により、checker 側の acceptance surface は増やさない。
pair-completion checker は source completion の証明に使い、target completion は
schedule shift theorem で運ぶ。

Status:
first hyperperiod 境界の reset completion は
`check_periodic_edf_checked_sidecar_first_hyperperiod_reset_completion` と
`check_periodic_edf_checked_sidecar_extracted_first_hyperperiod_reset_completion`
として外へ出した。これは既存 checker の
`check_periodic_hyperperiod_state_reset`、prefix/generated agreement、
`periodic_hyperperiod_state_reset_completed_in_schedule_upto` から構成される。

canonical extracted jobs について、hyperperiod 分だけ未来へ送る witness は
`extracted_periodic_shift_forward_job_by_hyperperiod` と
`extracted_periodic_shift_forward_deadline_between_pair` として追加済み。
また、shift 後 job が shift 後時刻の finite candidate enumeration に入ることは
`extracted_periodic_shift_forward_candidate_before` で証明済み。
これは membership bridge であり、EDF tie-break を保つ order-preserving enumeration
shift は未完了。

追加済みの中間補題:

- release range で candidate enumeration を filter しても task/index order を保つ
  `filter_map_periodic_jobs_by_release_range` と
  `enum_periodic_jobs_upto_filter_release_range`。
- order-preserving map が `choose_min_metric` / `choose_edf` の tie-break を保つ
  `min_metric_job_map_cmp`、`choose_min_metric_map_cmp`、
  `choose_edf_map_cmp`。
- extracted hyperperiod shift から release/deadline/cost/task 等式を取り出す
  `extracted_periodic_shift_forward_job_facts`。
- shifted prefix の service equality を仮定した `eligibleb` 保存と、
  shifted jobs 間の EDF metric 比較保存を示す
  `extracted_periodic_shift_forward_eligibleb`、
  `extracted_periodic_shift_forward_edf_metric_cmp`。

残る本質的な作業は、first-boundary reset を任意 hyperperiod boundary へ
反復輸送する schedule-level shift theorem と、その同じ shift theorem で
representative window service を target window service へ運ぶ theorem を証明すること。
DBF だけでは任意 boundary reset completion は出ないため、generated EDF schedule の
hyperperiod shift invariance を別 lemma として立てる必要がある。

### Phase F: representative obligation elimination

目的:
final theorem から `TransportClassRepresentativeObligation` を消す。

実装後の修正方針:
`sidecar.(checked_class_relevant_jobs)` に対して
`TransportClassRepresentativeObligation` を構成する方針は採らない。
この sidecar list は backlog check の入力としては検査されているが、
その list が semantic に complete であることは checker から復元できない。

代わりに、Rocq 側で生成できる
`transport_classes_rep_relevant_jobs T tasks offset jobs enumT codec classes`
に対して representative obligation を構成する。
この generated relevant list は coverage が定義と既存 lemma から出るため、
certificate generator を trusted にしない方針と整合する。

既存 theorem:

- `transport_class_representative_obligation_of_generated_checks`
- `transport_class_representative_obligation_of_generated_semantic_checks`
- `checked_transport_class_rep_completion_generated_sound`

追加済み wrapper:

```coq
Theorem check_periodic_edf_checked_sidecar_sound_with_completion_transport_generated_rep :
  check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
  PeriodicHyperperiodCompletionTransportObligation ... ->
  schedulable_by_on ... .
```

および checked block-source normalization を受け取る variant:

```coq
Theorem check_periodic_edf_checked_sidecar_extracted_checked_block_generated_rep_sound :
  check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
  PeriodicHyperperiodCheckedBlockSourceNormalizationObligation ... ->
  PeriodicHyperperiodServicePairTransportObligation ... ->
  PeriodicHyperperiodBoundaryResetCompletionObligation ... ->
  schedulable_by_on ... .
```

補助として次も追加済み:

- `generated_schedule_prefix_valid_schedule`
- `generated_periodic_edf_prefix_valid_schedule`
- `check_transport_classes_rep_backlog_generated_eq`

結果:
final theorem の外部仮定から `TransportClassRepresentativeObligation` を消せた。
ただし、消したのは generated relevant jobs 経由の theorem variant であり、
既存の sidecar relevant jobs 経由 theorem は互換性のため残す。

### Phase G: final theorem assembly

目的:
CSV/extracted checker の `true` だけから schedulability を得る。

組み立て順:

1. Phase B-D で
   `PeriodicHyperperiodBlockServiceSourceObligation` を構成する。 **Done**
2. Phase E で
   `PeriodicHyperperiodServicePairTransportObligation` と
   `PeriodicHyperperiodBoundaryResetCompletionObligation` を構成する。
   可能なら `PeriodicHyperperiodGeneratedSchedulePeriodicity` から両方を導く。
3. generated representative 経路で
   `PeriodicHyperperiodBlockServiceSourceObligation` を受け取る final theorem variant
   を追加し、それに渡す。

最終 wrapper:

```coq
Theorem check_periodic_edf_checked_sidecar_extracted_sound_closed :
  forall ts cert sidecar,
    check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true ->
    schedulable_by_on ... .
```

Extraction では theorem は抽出しない。抽出対象は checker のみ。

## 6. Implementation order

推奨順は次。

1. `checked normalization -> block-source obligation` を閉じる。
   **Done**
2. `TransportClassRepresentativeObligation` を generated relevant jobs 経由で消す
   extracted theorem variant を追加する。 **Done**
3. canonical jobs の exact cost / same-task hyperperiod shift 補題を追加する。 **Done**
4. arbitrary `target/x` から bounded `target0/x0` を構成する normalization theorem を追加する。 **Partial**
5. bounded `target0/x0` membership と canonical shift から
   `PeriodicHyperperiodBlockServiceSourceObligation` を構成する。 **Done**
   `check_hyperperiod_block_source_pair_in_certs = true` は finite concrete witness 用の
   補助に下げ、mainline では要求しない。
6. `PeriodicHyperperiodGeneratedSchedulePeriodicity` を boundary reset と service shift に分割して証明する。
   first-boundary reset completion の theorem 化は **Done**。
   forward job/pair shift と candidate membership shift は **Done**。
   order-preserving candidate enumeration shift、eligible/filter shift、
   `choose_edf` shift、generated schedule prefix shift は **Next**。
   その後、任意 boundary への反復 transport と service shift を閉じる。
7. final closed extracted theorem を追加する。
8. extraction list は checker 関数だけを維持し、proof-only theorem は抽出しない。
9. `make theories/TaskModels/Periodic/PeriodicEDFFinalCertificateChecker.vo` を通す。
10. `make build-periodic-edf-sched-csv` と `scripts/periodic_edf_schedulability_csv` を通す。
11. `make -j2` を通す。

## 7. Risks for the Rust design

Rust 側に scheduler trace detail を要求しないことが重要。

想定する Rust responsibilities:

- CSV parse
- taskset well-formedness の入力整形
- DBF / prefix / transport / post-reset certificate generation
- extracted checker の実行

Rust 側に要求しないこと:

- EDF schedule の意味論証明
- hyperperiod service transport の証明
- no-carry-in の証明
- runtime scheduler event の追加観測

主なリスク:

- certificate generator が `target0/x0/delta` の対応を作れない場合、
  checker は正しくても acceptance rate が下がる。
- generic periodic jobs に戻すと cost equality が失われるため、final theorem は
  extracted/canonical job model にまず固定する必要がある。
- EDF は同一 deadline の tie-break を candidate list order で解くため、
  candidate membership の対応だけでは generated schedule periodicity を証明できない。
  task order と job-index order を保つ enumeration shift が必要である。
- generated schedule periodicity theorem が閉じない場合、state-reset checker だけでは
  service-pair transport を補いきれない可能性がある。この場合は service shift を
  certificate obligation として一段残す。

## 8. Completion criteria

完了条件は次。

- `check_periodic_edf_checked_sidecar_extracted_sound_closed` が追加される。
- その theorem の仮定は
  `check_periodic_edf_checked_sidecar_extracted ts cert sidecar = true`
  だけになる。
- `Admitted` や未解決 Prop obligation は残さない。
- extracted Haskell checker は theorem ではなく boolean checker のみを含む。
- CSV script は既存の `schedulable` / failure diagnostics を維持する。
- `make -j2` が通る。
