## 結論

できる。
ただし、これは **ブラックボックスから唯一の真のモデルを抽出する** というより、**実OS trace によって反証されない最小の scheduler model を Rocq 上で同定し、checker と theorem で育てる** 研究になる。

この方向は、既存の **black-box model learning** や **process mining / conformance checking** に近い。model learning は入力を与えて出力を観測し、black-box の状態機械モデルを構成する手法であり、process mining でも event log からモデル発見・適合性検査を行う。ただし event log は観測例にすぎず、不完全で過学習しうる点が重要である。([labri.fr][1])

## RocqSched での言い換え

提案は次の形になる。

```text
実OS trace
  -> normalize
  -> candidate scheduler model に照合
  -> Rocq checker を Extraction
  -> 反例 trace を得る
  -> model / event alphabet / proof obligation を修正
  -> 再度 trace を取る
```

これは **trace-guided certified model extraction** である。

今回の Awkernel 1 worker core の成果は、この最小ケースである。

```text
Awkernel trace
  -> 1 worker projection
  -> FIFO / scheduler-facing acceptance
  -> extracted Haskell checker
```

ロードマップ上も、OS operational trace から `sched t c` を導出し、`service` / `completed` と接続し、その後 abstract policy と concrete machine の refinement を示す流れが置かれている。

## 重要な制約

有限 trace だけではモデルは一意に決まらない。

例えば、同じ trace を以下の複数モデルが同時に説明できる。

```text
FIFO
priority scheduler だが全 task の priority が同じ
EDF scheduler だが deadline 順が arrival 順と一致
RR scheduler だが quantum が十分大きい
```

したがって必要なのは「抽出」だけでなく、**識別 workload** である。

```text
FIFO と priority を分ける workload
priority と EDF を分ける workload
RR と FIFO を分ける workload
partitioned と global を分ける workload
work-conserving と non-work-conserving を分ける workload
```

つまり研究の核は、

```text
model inference + certified conformance checking + distinguishing workloads
```

になる。

## 分類は可能である

分類軸は次のように作れる。

```text
1. queue topology
   single queue / per-CPU queue / global queue / clustered queue / work-stealing

2. choice rule
   FIFO / RR / priority / EDF / fair-share / vruntime-like / heuristic

3. multicore policy
   partitioned / global / clustered / affinity-aware / migration-enabled

4. preemption rule
   non-preemptive / timer-preemptive / wakeup-preemptive / IPI-preemptive

5. service semantics
   immediate dispatch / delayed handoff / bounded handoff / lazy balancing

6. guarantee class
   no-duplication / work-conserving / priority-respecting / bounded waiting /
   starvation-free / bounded tardiness
```

既存の整理でも、FIFO・RR・prioritized FIFO・EDF について、それぞれ証明すべき性質が分けられている。たとえば RR では rotation・bounded waiting・timer/quantum correctness、EDF では earliest-deadline・global top-`m`・interference・bounded tardiness が主な検査対象になる。

## Rocq 上の基本形

分類器は、単なる Haskell スクリプトではなく、Rocq の model family から Extraction するのがよい。

```coq
Record SchedulerModel := {
  model_state : Type;
  model_init  : model_state;

  model_step :
    model_state -> ObsEvent -> option model_state;

  model_accepts_trace :
    list ObsEvent -> bool;
}.

Record ModelClass := {
  class_id : ModelId;
  class_model : SchedulerModel;
  class_features : list SchedulerFeature;
}.

Definition trace_fits_model
  (M : SchedulerModel)
  (tr : list ObsEvent) : bool :=
  model_accepts_trace M tr.

Definition indistinguishable_on
  (M1 M2 : SchedulerModel)
  (traces : list (list ObsEvent)) : Prop :=
  forall tr,
    In tr traces ->
    trace_fits_model M1 tr = trace_fits_model M2 tr.
```

次に、複数 candidate model に対する classifier を作る。

```coq
Definition classify_trace
  (models : list ModelClass)
  (tr : list ObsEvent)
  : list ModelId :=
  filter_map
    (fun C =>
       if trace_fits_model C.(class_model) tr
       then Some C.(class_id)
       else None)
    models.
```

この形にすれば、Haskell 側では、

```text
trace を入力
-> 通る model class 一覧
-> 落ちた model と最初の反例 index
```

を返せる。

## 次に作るべきもの

実装対象は次である。

```text
theories/Operational/TraceLearning/Observation.v
theories/Operational/TraceLearning/SchedulerModel.v
theories/Operational/TraceLearning/ModelClasses.v
theories/Operational/TraceLearning/Classifier.v
theories/Operational/TraceLearning/DistinguishingWorkloads.v
theories/Operational/TraceLearning/TraceLearningExtraction.v
```

TODO は次である。

```text
1. ObsEvent を Awkernel 固有形式から分離する
2. FIFO / RR / priority / EDF の recognizer を定義する
3. per-CPU / global / clustered の queue topology recognizer を定義する
4. classify_trace を Extraction する
5. 反例 index と失敗理由を返す
6. FIFO-vs-priority, FIFO-vs-RR, partitioned-vs-global の識別 workload を作る
7. accepted model から scheduler-facing theorem へ接続する
```

## 研究上の強み

この方向は、CertiKOS/mC2 のように最初から実装全体を証明するのとは違う。CertiKOS は contextual refinement により concrete multicore kernel と高位仕様を結ぶが、これは white-box に近い。

一方こちらは、

```text
実OSを black-box / gray-box として扱う
trace から scheduler model を同定する
Rocq で model class と conformance checker を保証する
複数OSを同じ分類軸で比較する
```

という方向である。

特に、既存研究では global EDF、top-`m` selection、migration correctness、fairness、bounded tardiness を concrete multicore scheduler まで end-to-end に接続した機械化例は少ないと整理されている。
したがって、**「実OS trace から certified scheduler taxonomy を作る」** はかなり良い研究テーマになる。

## まとめ

可能である。
ただし名前は「完全な model extraction」より、

```text
Trace-Guided Certified Scheduler Model Inference
```

または

```text
Certified Taxonomy of OS Schedulers from Execution Traces
```

が正確である。

次の一手は、Awkernel 1 worker FIFO checker を一般化して、**複数 scheduler model を同時に当てる classifier** にすることである。

[1]: https://www.labri.fr/perso/anca/Games/Bib/vaandrager-model-learning.pdf "vaandrager-model-learning.pdf"
