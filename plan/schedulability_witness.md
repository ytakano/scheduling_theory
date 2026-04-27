これ、AwkernelのNDJSONトレースから“機械で検査できるEDF証明（witness）”を作るための、実装に落としやすい青写真です。画像なしで一気に組めるよう、背景→手順→出力フォーマット→検査器の最小仕様までまとめます。

# ねらい（背景の超要約）

* **重い探索はジェネレータ側**（HaskellやRust）でやる。
* **小さい信頼コア**（Rocq/Coqや別の軽量チェッカ）で“証人（witness）”を再計算検査する。
* 形式は**SV‑COMPの検証Witness**に寄せる（GraphML/YAML）。既存のwitness検査器を流用しやすい。

---

# 実装ブループリント（3段階）

## 1) 時刻の正規化と決定的ソート

目的：各イベントに**単調増加の `global_ts`** を付与し、全順序にする。

* 入力：AwkernelのNDJSON（例）

  ```json
  {"cpu":0,"ts_tsc":12345678,"event":"irq","pkt_id":7,"local_seqno":42}
  ```
* 手順:

  1. **アンカー抽出**

     * RDTSCPのTSCサンプル（`ts_tsc`）
     * 同期取得したWallclock（NTP/ptpでも可）
  2. **TSC→global_ts 変換**

     * コア間TSCドリフト補正（起動時オフセット＋スケール）
     * `global_ts = a[cpu] + b[cpu]*ts_tsc` を最小二乗/既知校正で決定
  3. **安定ソート**

     * 主キー：`global_ts`
     * タイブレーク：`(cpu, local_seqno, pkt_id)` （決定的に）

> 産物：`global_ts` 付きの全順序イベント列。

---

## 2) 低レベル→スケジューラ意味イベントへ畳み込み

目的：EDF検査に必要な最小語彙に縮約し、“忙しい区間の前置き（busy‑prefix）”と“スケジュール断片”を抽出。

* 変換語彙：

  * `job-arrive(job_id, release, deadline, wcet)`
  * `job-start(job_id, cpu, t)` / `job-complete(job_id, t)`
  * `irq(kind, cpu, t)`（タイマ/IPI等）
* 抽出ロジック（単純な一次スキャン）：

  1. CPUごとに**連続稼働区間**を検出（アイドル→稼働→アイドル）
  2. 区間先頭からの**busy‑prefix候補**を記録
  3. 同時に「いつ誰を走らせたか」の**スケジュール断片**を吐く
* メタデータ参照：ジョブの`WCET`や`Cworst`は**タスク表**から合流（task_id→{period, deadline, wcet,...}）。

> 産物：意味イベント列＋busy‑prefixとスケジュール断片の集合。

---

## 3) window‑DBF の境界計算とWitness生成

目的：抽出したbusy‑prefixに対し**DBF（需要境界関数）**をローカル再計算し、**EDFで締切違反なし**を機械検査できる形に出力。

* 検査観点（単一/グローバルEDFに応じて拡張）：

  * 任意の窓幅 `Δ` に対し、**総要求量 ≤ 供給量（m×Δ）** をbusy‑prefixから示せること
  * スケジュール断片と到着列が**EDF規則（締切早い順、同時到着の安定タイブレーク）**に一致
* 出力：**SV‑COMP風Witness**（GraphML or YAML）

  * ノード：busy‑prefix / 窓 / ジョブ
  * エッジ：時間進行、選択（dispatch）、完了
  * 検査器は「列をなぞる＋ローカルDBF再計算」だけでOK（小さく保つ）

### ミニマルYAML例（概念）

```yaml
witness:
  format: "edf-dbfs"
  metadata:
    generator: "awk-witgen 0.1"
    trace_hash: "sha256:..."
  tasks:
    - id: T1; wcet: 3; deadline: 10
    - id: T2; wcet: 2; deadline: 7
  jobs:
    - id: J1; task: T1; release: 1000; deadline: 1010
    - id: J2; task: T2; release: 1001; deadline: 1008
  schedule_fragments:
    - cpu: 0; start: 1001; end: 1004; job: J2
    - cpu: 0; start: 1004; end: 1007; job: J1
  busy_prefixes:
    - cpu_set: [0]
      start: 1000
      checkpoints:
        - t: 1007
          window_demand_bound:
            windows:
              - width: 7
                demand: 5
                supply: 7
                ok: true
verification_goals:
  - kind: "no-deadline-miss"
    policy: "EDF"
    domain: "uniprocessor"
```

GraphML派なら、`<graph>`内に上記ノード/エッジを写像（SV‑COMPの`type="correctness_witness"`に倣う）。

---

# チェッカ（Trusted Checker）の最小仕様

* 入力：Witness（YAML/GraphML）＋（オプション）タスク表のハッシュ照合
* 検査：

  1. 参照整合性（ジョブ↔タスク、時間単調性、CPU占有不重複）
  2. EDF規則一致（締切昇順＋タイブレーク一致）
  3. **window‑DBF 再計算**（busy‑prefixの窓ごとに `Σ demand ≤ m×Δ`）
  4. 各ジョブの**完了時刻 ≤ 締切**
* 出力：`ACCEPT` / `REJECT`（失敗時は最小反例窓と当該ジョブ集合を報告）

> これにより、**検査器は小さく**（“再計算＋一致確認”のみ）、重い探索・抽出はジェネレータ側に寄せられる。

---

# 実装メモ（Awkernel向け）

* **トレース語彙**の固定：`sched_dispatch`, `preempt`, `irq_timer`, `ipi`, `job_release`, `job_complete` などを最小限に。
* **TSC正規化**ユニットテスト：コア跨ぎの ping‑pong タイムスタンプで単調性/誤差上限を確認。
* **決定的タイブレーク**：既存の`(cpu, local_seqno, pkt_id)`で衝突が残る場合は`trace_offset`を追加。
* **多コア拡張**：`m` コア分の供給 `m×Δ`、かつグローバルEDFの選抜`top‑m`一致を検査器に追加（後追いでOK）。

---

# すぐ書ける最小コンポーネント

1. `normalize_ts.rs`（or hs）：RDTSCP/Wallclockアンカー→`global_ts`付与＋安定ソート
2. `collapse_semantics.rs`：NDJSON→意味イベント列＋busy‑prefix抽出
3. `emit_witness.rs`：window‑DBFを計算してYAML/GraphMLを吐く
4. `witcheck`（Rocq/Coq or Haskell小バイナリ）：Witnessローカル再計算チェッカ

---

# 次の一歩（テスト順）

* 単一CPU・周期2タスクの合成トレースで**ACCEPT/REJECT**の両系を用意
* 実機ログ（Awkernel 1コア）で**TSC単調性**と**EDF一致**が通ることを確認
* そこから**m>1**、`irq`密度上昇、プリエンプト頻発ケースに拡張

---

