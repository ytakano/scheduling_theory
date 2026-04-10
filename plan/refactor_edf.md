はい。今の実装を見る限り、**EDF 最適性のために導入したが、実際には policy 非依存な補題**がかなりあります。特に `service_between`、`completed`/`missed_deadline` の言い換え、`service_before_release_zero`、`agrees_before` は `EDFLemmas.v` にありますが、内容は EDF 専用ではありません。さらに `service_job_eq_of_cpu_count_eq` や `swap_at` の低レベル解析は `EDFTransform.v` に、`single_cpu_only`・`mk_single_cpu`・`J_restrict` は `EDFOptimality.v` に置かれており、ここも分離余地が大きいです。いっぽうで `ScheduleModel.v` にはすでに `service_job`、`completed`、`eligible`/`ready`、`valid_schedule`、`cpu_count` の基礎補題があり、ここを基準に層を切るのが自然です。

おすすめの方針は、**「EDF 最適性の証明を薄くし、共通基盤・変換補題・EDF 固有補題の 3 層に分解する」**ことです。将来の roadmap でも、まず共通基盤を固めてから partitioned / global / OS semantics へ伸ばす構成になっているので、この切り方は今後の拡張とも整合します。

## 目標

最終的に次の形にするのがよいです。

* `ScheduleModel.v`
  定義と、ごく基本的な局所補題だけを置く
* `ScheduleFacts.v`
  `service_job` / `completed` / `missed_deadline` / 区間 service の一般補題
* `SchedulePrefix.v`
  `agrees_before` と prefix extensionality 一式
* `ScheduleTransform.v`
  schedule の局所変換に関する一般補題
* `SingleCPUView.v` あるいは `ScheduleRestriction.v`
  `mk_single_cpu`、`J_restrict`、single-CPU 化補題
* `UniPolicies/EDFLemmas.v`
  EDF 選択規則そのものに依存する補題だけ
* `UniPolicies/EDFTransform.v`
  first-violation witness と repair 構成だけ
* `UniPolicies/EDFOptimality.v`
  最終定理と、その直下の glue のみ

## 切り分け基準

まず全補題を次の 4 種にタグ付けしてください。

### 1. 完全に共通

EDF も FIFO も RR も使えるものです。

候補:

* `service_between`
* `completed_iff_service_ge_cost`
* `not_completed_iff_service_lt_cost`
* `missed_deadline_iff_*`
* `service_before_release_zero`
* `service_at_release_zero`
* `agrees_before`
* `agrees_before_service_job`
* `agrees_before_completed`
* `agrees_before_eligible`

これらは EDF 依存がないので、`ScheduleFacts.v` / `SchedulePrefix.v` へ出すべきです。

### 2. 一般的な schedule 変換

EDF 最適性で使っているが、理屈自体は EDF 固有ではないものです。

候補:

* `service_job_eq_of_cpu_count_eq`
* `swap_at`
* `swap_at_same_outside`
* `cpu_count_1_swap_at_*`
* `swap_at_service_prefix_before_t1`

これらは将来、FIFO や別の交換論法でも再利用しやすいので、`ScheduleTransform.v` に集める価値があります。

### 3. 単一 CPU への制限・部分集合への制限

最適性証明の準備だが EDF に閉じていない層です。

候補:

* `single_cpu_only`
* `mk_single_cpu`
* `J_restrict`
* それらの `service` / `valid` / `feasible` 保存補題

これは `SingleCPUView.v` か `ScheduleRestriction.v` に切り出すのがよいです。

### 4. EDF 固有

ここは残します。

候補:

* `choose_edf_*`
* `edf_violation_at_*`
* `first_violation_has_repair_witness`
* `repair_first_violation`
* `repair_pushes_first_violation_forward`
* 最終 optimality theorem

これは `UniPolicies/EDF*` 側に残すべきです。

## 実施順の plan

### Phase 1: 依存グラフを固定する

最初に、各補題に次の印を付けます。

* `G`: policy 非依存
* `T`: schedule transform 一般
* `S`: single-CPU / restriction
* `E`: EDF 固有

この段階ではコードはまだ動かさず、**補題一覧だけを作る**のが大事です。
目的は「どこまで動かすと循環 import が起きるか」を先に見抜くことです。

### Phase 2: `ScheduleFacts.v` を新設する

最初の切り出し対象は `service_between` 周辺です。ここは最も安全です。

ここに入れる候補:

* `service_between`
* `service_between_eq`
* `service_between_0_r`
* `service_between_refl`
* `service_between_split`
* `completed_iff_service_ge_cost`
* `not_completed_iff_service_lt_cost`
* `missed_deadline_iff_*`
* `service_before_release_zero`
* `service_at_release_zero`

このとき、**命名も合わせて整える**のがよいです。
たとえば今が `service_job` なので、`service_between` は `service_job_between` に改名する案が強いです。そうすると API が揃います。

### Phase 3: `SchedulePrefix.v` を新設する

次に prefix agreement を独立させます。

ここに入れる候補:

* `agrees_before`
* `agrees_before_weaken`
* `agrees_before_refl`
* `agrees_before_sym`
* `agrees_before_trans`
* `cpu_count_agrees_at`
* `agrees_before_service_job`
* `agrees_before_completed`
* `agrees_before_eligible`
* `agrees_before_ready`
* `eligibleb_agrees_before`
* `candidates_of_agrees_before` のうち EDF 非依存部分

ただし `candidates_of_agrees_before` や `choose_edf_agrees_before` は bridge / EDF に依るので、ここは分離して

* prefix の一般部は `SchedulePrefix.v`
* dispatch/EDF に触れる部は現状ファイル
  に分けるのが安全です。

### Phase 4: `ScheduleTransform.v` を新設する

次に交換論法の下層を切り出します。

ここに入れる候補:

* `swap_at`
* `swap_at_same_outside`
* `swap_at_t1`
* `swap_at_t2`
* `cpu_count_1_swap_at_*`
* `cpu_count_1_some_eq`
* `cpu_count_1_some_neq`
* `service_job_eq_of_cpu_count_eq`
* `swap_at_service_prefix_before_t1`
* 他 policy 非依存の swap/service 補題

ここでは **「swap による service 変化」までを一般層に寄せるか** が分岐点です。
おすすめは、`j1/j2` の役割が EDF の前後関係に依存しないところまでは共通化し、
「deadline 比較を使う improve / not-hurt」は EDF 側に残す、です。

### Phase 5: `SingleCPUView.v` を作る

`EDFOptimality.v` 冒頭の前処理を切り離します。

ここに入れる候補:

* `single_cpu_only`
* `mk_single_cpu`
* `mk_single_cpu_*`
* `J_restrict`
* `J_restrict_*`

これは EDF だけでなく、将来「任意の multicore feasible schedule を単一 CPU / 部分集合に落とす」議論で再利用できます。特に partitioned や refinement でも効きます。

### Phase 6: EDF ファイルを薄くする

ここまで終わったら EDF 側を整理します。

* `EDFLemmas.v`
  EDF 選択・候補集合・違反 witness だけ残す
* `EDFTransform.v`
  repair schedule の構成と EDF 固有の repair correctness だけ残す
* `EDFOptimality.v`
  定理本体と、proof orchestration だけ残す

理想は、`EDFOptimality.v` を開いたときに

* 汎用 service 補題
* 汎用 prefix 補題
* 汎用 transform 補題
* EDF 固有補題
  を組み合わせているのが一目でわかる状態です。

## 各 Phase の完了条件

各段階で次を満たすようにすると安全です。

* 移したファイルが **`UniPolicies.EDF` を import しない**
* `EDFOptimality.v` の証明本文が短くなる
* 補題の statement が変わるなら、名前と用途がより明確になる
* `_CoqProject` と import 階層に循環がない
* 既存の examples / partitioned 側が壊れていない

## 実際の作業順としてはこれが最小リスクです

1. `service_between` 群を移す
2. `agrees_before` 群を移す
3. `service_job_eq_of_cpu_count_eq` を移す
4. `single_cpu_only` / `mk_single_cpu` / `J_restrict` を移す
5. EDF ファイル内の import を整理する
6. 最後に命名をそろえる

この順がよい理由は、前半 3 つは **statement が安定していて証明も一般的**だからです。反対に `J_restrict` や repair 系は依存が多いので後半に回すのが安全です。

## 命名のおすすめ

いまの状態からだと、次の命名がわかりやすいです。

* `ScheduleFacts.v`
* `SchedulePrefix.v`
* `ScheduleTransform.v`
* `ScheduleRestriction.v`
