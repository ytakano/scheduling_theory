(**
  example_feasible.v
  ==================
  Job・Schedule・feasible の具体例

  【型の説明】
  - Job     : ジョブを表すレコード。
                job_release  : 解放時刻（いつ実行可能になるか）
                job_cost     : 実行に必要なタイムスロット数
                job_abs_deadline : この時刻までに完了しなければならない
  - Schedule : Time -> CPU -> option JobId
               「時刻 t に CPU c でどのジョブが動いているか」を返す関数。
               Some j なら job j が動いている、None なら何も動いていない。
  - feasible jobs m sched
               CPUが m 台のスケジュール sched において、
               全ジョブが締切を守る（missed_deadline になるジョブがない）こと。
*)

From Stdlib Require Import Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.

(* ================================================================= *)
(** ** Example 1: Feasible な例                                       *)
(* ================================================================= *)

(**
  設定:
    - CPU 1 台 (m = 1, CPU番号 0 のみ)
    - ジョブ 1 本 (JobId = 0)
    - Job: release=0, cost=2, deadline=3
           → 時刻 0 から実行可能、2 タイムスロット必要、時刻 3 までに完了

  スケジュール:
    t=0: CPU 0 → job 0 を実行
    t=1: CPU 0 → job 0 を実行
    t≥2: CPU 0 → 何も実行しない (None)

  タイムライン:
    t:  0   1   2   3
    CPU0: [j0][j0][ ][ ]
                 ↑ deadline=3 のとき、累積実行量 = 2 ≥ cost=2 → 完了 ✓
*)

Definition job_ex1 : Job := mkJob 0 0 0 2 3. (* task=0, arrival=0, release=0, cost=2, deadline=3 *)

(** 全 JobId に対して同じジョブを返す定数関数 *)
Definition jobs_ex1 (j : JobId) : Job := job_ex1.

(** スケジュール: t < 2 かつ CPU 0 のとき job 0 を実行 *)
Definition sched_ex1 (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    if Nat.ltb t 2 then Some 0
    else None
  else None.

(** 補助補題: cpu_count の上界（cpu_count ≤ m を使う） *)

Lemma cpu_count_le_m : forall m sched j t,
    cpu_count sched j t m <= m.
Proof.
  induction m as [| m' IH]; intros sched j t.
  - simpl. lia.
  - simpl.
    pose proof (IH sched j t) as Hle.
    destruct (runs_on sched j t m'); simpl; lia.
Qed.

Lemma service_le_m_mul_t : forall m sched j t,
    service_job m sched j t <= m * t.
Proof.
  intros m sched j.
  induction t as [| t' IH].
  - simpl. lia.
  - rewrite service_job_step.
    pose proof (cpu_count_le_m m sched j t') as Hle.
    lia.
Qed.

(** Job 0 は時刻 3 までに完了している *)
Lemma ex1_job0_completed : completed jobs_ex1 1 sched_ex1 0 3.
Proof.
  unfold completed, jobs_ex1, job_ex1, sched_ex1.
  simpl.
  lia.
Qed.

(** Job 0 は締切を守っている（not missed_deadline） *)
Lemma ex1_job0_meets_deadline : ~missed_deadline jobs_ex1 1 sched_ex1 0.
Proof.
  unfold missed_deadline.
  intro H.
  exact (H ex1_job0_completed).
Qed.

(* ================================================================= *)
(** ** Example 2: Feasible なスケジュールが存在しない例              *)
(* ================================================================= *)

(**
  設定:
    - CPU 1 台 (m = 1)
    - ジョブ 1 本 (JobId = 0)
    - Job: release=0, cost=3, deadline=2
           → 時刻 0 から実行可能、3 タイムスロット必要、時刻 2 までに完了

  なぜ不可能か:
    締切 2 までに実行できる最大タイムスロット数は:
      t=0, t=1 の 2 スロット (CPU 1 台) = 2 < cost=3

    どんなスケジュールを選んでも service ≤ 2 < 3 = cost
    → 必ず missed_deadline になる。

  タイムライン:
    t:  0   1   [deadline=2]
    CPU0: [??][??]
              ↑ 最大でも 2 タイムスロット実行できるが cost=3 には足りない ✗
*)

Definition job_ex2 : Job := mkJob 0 0 0 3 2. (* task=0, arrival=0, release=0, cost=3, deadline=2 *)

Definition jobs_ex2 (j : JobId) : Job := job_ex2.

(** どんなスケジュールを使っても job 0 は締切を守れない *)
Lemma ex2_any_sched_misses : forall sched, missed_deadline jobs_ex2 1 sched 0.
Proof.
  intro sched.
  unfold missed_deadline, completed, jobs_ex2, job_ex2.
  simpl.
  pose proof (service_le_m_mul_t 1 sched 0 2) as Hle.
  simpl in Hle.
  lia.
Qed.

(** したがって、jobs_ex2 は schedulable ではない *)
Lemma ex2_not_schedulable : ~schedulable jobs_ex2 1.
Proof.
  unfold schedulable.
  intros [sched [_ Hfeas]].
  unfold feasible in Hfeas.
  exact (Hfeas 0 (ex2_any_sched_misses sched)).
Qed.
