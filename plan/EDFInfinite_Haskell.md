`EDFInfiniteSchedulability.v` をこのまま手証明で伸ばすのではなく、**有限 concrete task set から有限 certificate を生成し、Rocq 側では certificate checker の soundness だけを証明する**方式に切り替えるのが現実的である。

現在の実装はすでにその方向に近い。`dbf_test_by_cutoff` で scalar DBF を有限 cutoff に落とし、`dbf_check_by_cutoff` で `forall t, taskset_periodic_dbf ... t <= t` を得ている。また `check_edf_infinite_cert cert_ex_generic = true`、prefix / transport / DBF certificate、最終的な `periodic_edf_schedulable_by_classical_dbf_generated_from_infinite_obligations` への接続も入っている。

ただし、重い部分はまだ残っている。特に no-carry-in / backlog-free の証明が、prefix table、backlog matrix、transport class、completion target の個別手証明になっている。これは Prosa / POET 的には「Rocq に探索させる」べきではなく、「外部ツールが witness を出し、Rocq が小さい checker で検査する」べき部分である。Prosa は Rocq で機械検査可能な schedulability analysis を蓄積する枠組みであり、POET は YAML 入力から response-time bound と Rocq certificate を生成し、未検証ツールを信頼せず Rocq toolchain で certificate を検査する設計である。([Prosa][1])

## 方針

やるべきことは、`EDFInfiniteSchedulability.v` を「証明本体」から「チュートリアル / regression example」へ降格し、次の3層に分離することである。

1. **Demand 側**
   `dbf_test_by_cutoff` / `window_dbf_test_by_cutoff` を主経路にする。zero-offset なら classical scalar DBF から window DBF へ落とせるので、schedule prefix を無限に見る必要はない。現在の `PeriodicConcreteAnalysis.v` の方向でよい。

2. **Prefix schedule 側**
   `prefix_slots` が EDF の finite generated schedule と一致すること、basis jobs が完了していること、backlog matrix が release 前完了を表すことを、手証明ではなく boolean checker にする。

3. **Transport 側**
   hyperperiod ごとの job shift、completion offset、backlog offset を certificate 化する。例では hyperperiod `35`、task0 shift `7`、task1 shift `5` が使われているので、これを一般化する。現在の generated certificate はすでにこのデータを持っているが、soundness はまだかなり手作業である。

Prosa の busy-window 形式化も参考になる。ECRTS 2020 の Prosa 系 busy-window 研究は、busy-window 原理を「小さく明示的な仮定集合」へ分解し、そこから scheduler / workload / preemption ごとの具体解析へ refine する構成を取っている。このプロジェクトでも、no-carry-in / backlog-free を巨大な個別証明ではなく、明示的な finite witness 仮定へ分解するのが合う。([drops.dagstuhl.de][2])

## 推奨ロードマップ

### Phase 1: `EDFInfiniteSchedulability.v` の肥大化を止める

**目的:** tutorial ファイルをこれ以上 proof engineering の本体にしない。

TODO:

* `Tutorials/EDFInfiniteSchedulability.v` は regression example として残す。
* 証明本体を次の新規ファイルへ移す。

  * `theories/TaskModels/Periodic/PeriodicEDFConcreteInfiniteCertificate.v`
  * `theories/TaskModels/Periodic/PeriodicEDFConcreteInfiniteCertificateChecker.v`
  * `theories/TaskModels/Periodic/PeriodicEDFConcreteInfiniteCertificateSoundness.v`
* `Tutorials/Generated/EDFInfiniteSchedulabilityCert_ex.v` は generated artifact の例として残す。
* `cert_ex_dbf_generic` は現在 cutoff `0` の小さな table になっており、実際の global DBF 証明は別途 `cert_ex_dbf_test_by_cutoff_true` に依存している。ここを統合する。

### Phase 2: DBF checker を正式な concrete infinite entry point にする

対象ファイル:

* `theories/TaskModels/Periodic/PeriodicConcreteAnalysis.v`
* `theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v`

TODO:

* `dbf_test_by_cutoff` を infinite EDF certificate の正式 demand field にする。
* `EDFDBFCert` を次のどちらかに整理する。

  * `dbf_test_by_cutoff tasks enumT = true` を certificate checker 内で直接検査する。
  * または `dbf_ok_table` に cutoff 全体の結果を入れ、`dbf_cutoff = scalar_dbf_cutoff_bound tasks enumT` を checker が検査する。
* large concrete task set 用に `nat` ではなく `N` / `Z` ベースの executable DBF checker を追加する。

Rocq スケルトン:

```coq
Record EDFConcreteDBFCert := {
  dbf_cert_cutoff : Time;
  dbf_cert_table : list bool
}.

Definition check_concrete_dbf_cert
    (tasks : TaskId -> Task)
    (enumT : list TaskId)
    (c : EDFConcreteDBFCert) : bool :=
  Nat.eqb c.(dbf_cert_cutoff) (scalar_dbf_cutoff_bound tasks enumT)
  && Nat.eqb (length c.(dbf_cert_table)) (S c.(dbf_cert_cutoff))
  && forallb
       (fun t =>
          nth t c.(dbf_cert_table) false
          && (taskset_periodic_dbf tasks enumT t <=? t))
       (seq 0 (S c.(dbf_cert_cutoff))).

Theorem check_concrete_dbf_cert_sound :
  forall tasks enumT c,
    NoDup enumT ->
    (forall τ, In τ enumT -> 0 < task_period (tasks τ)) ->
    check_concrete_dbf_cert tasks enumT c = true ->
    forall t, taskset_periodic_dbf tasks enumT t <= t.
Admitted.
```

### Phase 3: prefix semantics を verified checker 化する

対象ファイル:

* `theories/TaskModels/Periodic/PeriodicEDFCertificate.v`
* `theories/TaskModels/Periodic/PeriodicEDFCertificateSoundness.v`
* 新規 `PeriodicEDFPrefixChecker.v`

現在は `EDFPrefixCertSemantics` をユーザが手で与えている。これを checker にする。

TODO:

* `slot_schedule : list (option JobId) -> Schedule` を定義する。
* `service_of_slots`、`completed_by_slots`、`released_by_job`、`eligible_by_slots` を executable にする。
* 各時刻 `t < prefix_horizon` で、slot が EDF choice と一致することを boolean で確認する。
* `prefix_completed_by` が実際の service から正しいことを boolean で確認する。
* `prefix_backlog_free_matrix` が release-order と completion を表すことを boolean で確認する。
* soundness theorem で `EDFPrefixCertSemantics` を自動生成する。

Rocq スケルトン:

```coq
Definition schedule_of_slots
    (slots : list (option JobId)) : Schedule :=
  fun t c =>
    if Nat.eqb c 0 then nth t slots None else None.

Definition check_prefix_completed
    (jobs : JobId -> Job)
    (slots : list (option JobId))
    (basis : list JobId)
    (completed_by : list Time) : bool :=
  forallb
    (fun '(j, t) =>
       job_cost (jobs j) <=?
       certified_service_prefix slots j t)
    (combine basis completed_by).

Definition check_prefix_cert_semantic
    (jobs : JobId -> Job)
    (c : EDFPrefixCert JobId) : bool :=
  check_prefix_cert c
  && check_prefix_completed jobs
       c.(prefix_slots)
       c.(prefix_basis_jobs)
       c.(prefix_completed_by)
  && check_prefix_backlog_matrix jobs c.

Theorem check_prefix_cert_semantic_sound :
  forall jobs c,
    check_prefix_cert_semantic jobs c = true ->
    EDFPrefixCertSemantics jobs c (schedule_of_slots c.(prefix_slots)).
Admitted.
```

### Phase 4: generated EDF schedule との一致を certificate から示す

対象ファイル:

* `theories/TaskModels/Periodic/PeriodicEDFPrefixCoherence.v`
* `theories/TaskModels/Periodic/PeriodicEDFInfiniteBridge.v`
* 新規 `PeriodicEDFGeneratedPrefixChecker.v`

現在の tutorial は `cert_prefix_sched_ex_local_scheduler`、`generated_prefix_slot_ex` などで、prefix schedule が generated EDF schedule と一致することを手で示している。これは horizon が伸びると破綻する。

TODO:

* `check_prefix_edf_choice_at` を作る。
* 各 `t < H` について、certificate slot が `choose edf_generic_spec ...` と一致することを boolean で検査する。
* 既存の `local_scheduler_matches_generated_schedule_prefix` を使い、boolean checker から `agrees_before` へ接続する。
* `do H destruct` 型の証明を完全に消す。

### Phase 5: transport を一般化する

対象ファイル:

* `theories/TaskModels/Periodic/PeriodicEDFTransport.v`
* `theories/TaskModels/Periodic/PeriodicEDFTransportChecker.v`
* `theories/TaskModels/Periodic/PeriodicEDFTransportSoundness.v`

現在の example では、task0 は `k -> k + 7*q`、task1 は `k -> k + 5*q` へ移す証明を手で行っている。これは具体 task set ごとに同じ形の証明を量産することになる。

TODO:

* hyperperiod `hp` を計算する。
* 各 task `τ` について `task_shift τ = hp / period τ` を定義する。
* `job_id_of τ (r + task_shift τ * q)` を transport 対象にする。
* representative job の completion/backlog offset を certificate で持つ。
* `q = 0` は prefix certificate、`q > 0` は transport theorem で処理する。
* `completion_target_ex` のような具体例専用 inductive を廃止する。

Rocq スケルトン:

```coq
Record PeriodicEDFTransportObligation := {
  transport_hp : Time;
  transport_task_shift : TaskId -> nat;
  transport_prefix_horizon : Time
}.

Definition shifted_job
    (job_id_of : TaskId -> nat -> JobId)
    (shift : TaskId -> nat)
    (τ : TaskId) (r q : nat) : JobId :=
  job_id_of τ (r + shift τ * q).

Theorem periodic_transport_backlog_sound :
  forall T tasks offset jobs enumT codec cert,
    check_transport_cert cert = true ->
    (* algebraic shift obligations *)
    (* representative completion/backlog obligations *)
    forall j,
      periodic_jobset T tasks offset jobs j ->
      periodic_edf_backlog_free_before_release
        T tasks offset jobs
        (S (job_abs_deadline (jobs j)))
        (generated_periodic_edf_schedule_upto
           T tasks offset jobs
           (S (job_abs_deadline (jobs j))) enumT codec)
        j.
Admitted.
```

### Phase 6: final theorem を certificate 一発にする

対象ファイル:

* `theories/TaskModels/Periodic/PeriodicEDFConcreteInfiniteCertificateEntryPoints.v`

TODO:

* ユーザ向け theorem を次の形にする。
* `EDFInfiniteSchedulability.v` 側では、task set 定義、codec、generated certificate import、`vm_compute; reflexivity` だけにする。
* それ以外の証明を tutorial から消す。

Rocq スケルトン:

```coq
Record PeriodicEDFConcreteInfiniteCert
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job)
    (enumT : list TaskId)
    (codec : PeriodicCodec T tasks offset jobs) := {
  concrete_prefix_cert : EDFPrefixCert JobId;
  concrete_transport_cert : EDFTransportCert JobId;
  concrete_dbf_cert : EDFConcreteDBFCert
}.

Definition check_periodic_edf_concrete_infinite_cert
    T tasks offset jobs enumT codec
    (c : PeriodicEDFConcreteInfiniteCert T tasks offset jobs enumT codec)
  : bool :=
  check_prefix_cert_semantic jobs c.(concrete_prefix_cert)
  && check_transport_cert c.(concrete_transport_cert)
  && check_concrete_dbf_cert tasks enumT c.(concrete_dbf_cert).

Theorem periodic_edf_schedulable_by_checked_concrete_infinite_cert :
  forall T tasks offset jobs enumT codec cert,
    well_formed_periodic_tasks_on T tasks ->
    NoDup enumT ->
    (forall τ, T τ -> In τ enumT) ->
    (forall τ, In τ enumT -> T τ) ->
    (forall τ, In τ enumT -> offset τ = 0) ->
    check_periodic_edf_concrete_infinite_cert
      T tasks offset jobs enumT codec cert = true ->
    schedulable_by_on
      (periodic_jobset T tasks offset jobs)
      (edf_scheduler
         (periodic_candidates_before
            T tasks offset jobs enumT codec))
      jobs 1.
Admitted.
```

## 実装順の TODO

1. `EDFDBFCert` を `dbf_test_by_cutoff` と整合させる。
   **File:** `PeriodicEDFCertificate.v`, `PeriodicConcreteAnalysis.v`

2. `schedule_of_slots` と `check_prefix_cert_semantic` を追加する。
   **File:** `PeriodicEDFPrefixChecker.v`

3. `EDFPrefixCertSemantics` を checker から導出する theorem を追加する。
   **File:** `PeriodicEDFPrefixCheckerSoundness.v`

4. `generated_periodic_edf_schedule_upto` と certificate prefix の一致を boolean checker 化する。
   **File:** `PeriodicEDFGeneratedPrefixChecker.v`

5. hyperperiod transport を task-generic にする。
   **File:** `PeriodicEDFTransport.v`, `PeriodicEDFTransportChecker.v`

6. no-carry-in bridge を `prefix + transport` から自動導出する。
   **File:** `PeriodicEDFConcreteInfiniteCertificateSoundness.v`

7. final wrapper を追加する。
   **File:** `PeriodicEDFConcreteInfiniteCertificateEntryPoints.v`

8. `Tutorials/EDFInfiniteSchedulability.v` を 200〜300 行程度に縮小する。
   **File:** `Tutorials/EDFInfiniteSchedulability.v`

## 実用上の注意

完全な exact analysis は hyperperiod 依存になり得る。したがって task period の lcm が巨大な concrete task set では、Rocq 内の `vm_compute` だけで全探索するのは現実的でない。この場合は、POET と同じく「外部 generator が certificate を作る、Rocq は certificate を検査する」方式にするべきである。POET も、Rocq の unary number 表現による scalability 問題を認識し、CoqEAL refinement を使って実用サイズへ近づけている。([Prosa][3])

[1]: https://prosa.mpi-sws.org/ "Prosa: A Foundation for Formally Proven Schedulability Analysis"
[2]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECRTS.2020.22 "Abstract Response-Time Analysis: A Formal Foundation for the Busy-Window Principle"
[3]: https://prosa.mpi-sws.org/poet.html "POET: A Foundational Response-Time Analysis Tool"
