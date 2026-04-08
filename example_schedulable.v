(**
  example_schedulable.v
  =====================
  schedulable_by・schedulable_by_on の使用例

  【定義の概要】
  - schedulable_by alg jobs m
      alg が生成するスケジュールが valid かつ feasible（全ジョブが締切を守る）
  - schedulable_by_on J alg jobs m
      alg が生成するスケジュールが valid かつ J 上で feasible
      （J に属するジョブのみ締切を守る）

  【Scheduler は抽象 Parameter】
  具体的アルゴリズムは定義されていない。
  本ファイルでは Variable/Hypothesis を用い、あるアルゴリズムが特定の
  スケジュールを生成すると仮定して schedulable_by_on を導出する。

  【注意: jobs_sc の全域性】
  jobs_sc は全 JobId に同じジョブ（cost=2）を返す定数関数。
  sched_sc は job 0 しか実行しないため、j ≠ 0 は締切を守れない。
  よって feasible_schedule（全ジョブ）ではなく
  feasible_schedule_on (fun j => j = 0) を証明し、
  schedulable_by_on を直接導出する。
*)

From Stdlib Require Import Arith Arith.PeanoNat Lia.
Require Import Base.
Require Import Schedule.

(* Abstract lemmas (schedulable_by_implies_feasible,
   schedulable_by_implies_schedulable_by_on, schedulable_by_on_monotone)
   are proved in Schedule.v. *)

(* ================================================================= *)
(** ** 具体例: schedulable_by_on の証明                               *)
(* ================================================================= *)

(**
  設定:
    - CPU 1 台 (m = 1, CPU番号 0 のみ)
    - 追跡ジョブ集合: J = (fun j => j = 0)（job 0 のみ）
    - Job: task=0, arrival=0, release=0, cost=2, deadline=3
           → 時刻 0 から実行可能、2 タイムスロット必要、時刻 3 までに完了

  スケジュール:
    t=0: CPU 0 → job 0 を実行
    t=1: CPU 0 → job 0 を実行
    t≥2: CPU 0 → 何も実行しない (None)

  タイムライン:
    t:  0   1   2   3
    CPU0: [j0][j0][ ][ ]
                 ↑ deadline=3 のとき、累積実行量 = 2 >= cost=2 → 完了 ✓
*)

Definition job_sc : Job := mkJob 0 0 0 2 3.

(** 全 JobId に対して同じジョブを返す定数関数 *)
Definition jobs_sc (j : JobId) : Job := job_sc.

(** スケジュール: t < 2 かつ CPU 0 のとき job 0 を実行 *)
Definition sched_sc (t : Time) (cpu : CPU) : option JobId :=
  if Nat.eqb cpu 0 then
    if Nat.ltb t 2 then Some 0 else None
  else None.

Section SchedulableExample.

  Variable alg_sc : Scheduler.

  (** 仮説: アルゴリズム alg_sc は jobs_sc・1 CPU で sched_sc を生成する *)
  Hypothesis alg_sc_runs_sched_sc : run_scheduler alg_sc jobs_sc 1 = sched_sc.

  (* -------------------------------------------------------------- *)
  (** *** 補助補題: cpu_count の上界                                 *)
  (* -------------------------------------------------------------- *)

  (**
    sched_sc での cpu_count sched_sc 0 t 1 は 1 以下。
    CPU 0 のみが動き、その寄与は 0 または 1。
  *)
  Lemma sc_cpu_count_le_1 : forall t,
      cpu_count sched_sc 0 t 1 <= 1.
  Proof.
    intro t.
    simpl.
    unfold runs_on, sched_sc.
    rewrite Nat.eqb_refl.
    destruct (Nat.ltb t 2); simpl; lia.
  Qed.

  (**
    service_job 1 sched_sc 0 t ≤ t。
    帰納法: ステップごとに cpu_count ≤ 1 を使う。
  *)
  Lemma sc_service_le_t : forall t,
      service_job 1 sched_sc 0 t <= t.
  Proof.
    induction t as [| t' IH].
    - simpl. lia.
    - rewrite service_job_step.
      pose proof (sc_cpu_count_le_1 t') as Hle.
      lia.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** 有効スケジュール性                                         *)
  (* -------------------------------------------------------------- *)

  (**
    valid_schedule jobs_sc 1 sched_sc:
    割り当てられた全ジョブが eligible（リリース済み・未完了）。
    sched_sc で割り当てが発生するのは t < 2, cpu = 0 のときのみ（job 0）。
  *)
  Lemma sc_valid_schedule : valid_schedule jobs_sc 1 sched_sc.
  Proof.
    unfold valid_schedule.
    intros j t c Hlt_c Hrun.
    (* c < 1 → c = 0 *)
    assert (Hc0 : c = 0) by lia.
    subst c.
    (* sched_sc t 0 の展開 *)
    unfold sched_sc in Hrun.
    rewrite Nat.eqb_refl in Hrun.
    destruct (Nat.ltb t 2) eqn:Hlt_t.
    - (* t < 2, j = 0 *)
      injection Hrun as Hj.
      subst j.
      apply Nat.ltb_lt in Hlt_t.
      unfold eligible.
      split.
      + (* released: job_release job_sc = 0 ≤ t *)
        unfold released, jobs_sc, job_sc. simpl. lia.
      + (* ~completed: service_job 1 sched_sc 0 t < 2 *)
        unfold completed, jobs_sc, job_sc. simpl.
        intro Hcomp.
        pose proof (sc_service_le_t t) as Hle.
        lia.
    - (* Nat.ltb t 2 = false → sched_sc t 0 = None → 矛盾 *)
      discriminate.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** job 0 の完了                                              *)
  (* -------------------------------------------------------------- *)

  (**
    job 0 は時刻 3 までに累積実行量 2 ≥ cost=2 を達成している。
    service_job 1 sched_sc 0 3 を simpl で展開し lia で閉じる。
  *)
  Lemma sc_job0_completed : completed jobs_sc 1 sched_sc 0 3.
  Proof.
    unfold completed, jobs_sc, job_sc, sched_sc.
    simpl.
    lia.
  Qed.

  (**
    job 0 は締切を守る（missed_deadline にならない）。
  *)
  Lemma sc_job0_meets_deadline : ~missed_deadline jobs_sc 1 sched_sc 0.
  Proof.
    unfold missed_deadline.
    intro Hmiss.
    exact (Hmiss sc_job0_completed).
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** 部分的 feasibility                                        *)
  (* -------------------------------------------------------------- *)

  (**
    feasible_schedule_on (fun j => j = 0) jobs_sc 1 sched_sc:
    job 0 のみを追跡する場合、締切を守る。
  *)
  Lemma sc_feasible_schedule_on :
      feasible_schedule_on (fun j => j = 0) jobs_sc 1 sched_sc.
  Proof.
    unfold feasible_schedule_on.
    intros j Hj.
    subst j.
    exact sc_job0_meets_deadline.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** 主定理: schedulable_by_on                                 *)
  (* -------------------------------------------------------------- *)

  (**
    schedulable_by_on (fun j => j = 0) alg_sc jobs_sc 1:
    alg_sc が生成するスケジュールは job 0 について valid かつ feasible。
    仮説 alg_sc_runs_sched_sc で run_scheduler を sched_sc に書き換える。
  *)
  Theorem sc_schedulable_by_on :
      schedulable_by_on (fun j => j = 0) alg_sc jobs_sc 1.
  Proof.
    unfold schedulable_by_on.
    rewrite alg_sc_runs_sched_sc.
    split.
    - exact sc_valid_schedule.
    - exact sc_feasible_schedule_on.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** 単調性の適用例                                            *)
  (* -------------------------------------------------------------- *)

  (**
    schedulable_by_on_monotone の使用例:
    空集合（ジョブなし）でも trivially schedulable_by_on が成り立つ。
    包含 (fun _ => False) ⊆ (fun j => j = 0) を使い単調性で導出。
  *)
  Corollary sc_schedulable_by_on_empty :
      schedulable_by_on (fun _ : JobId => False) alg_sc jobs_sc 1.
  Proof.
    apply (schedulable_by_on_monotone
             (fun _ : JobId => False)
             (fun j => j = 0)
             alg_sc jobs_sc 1).
    - intros j Hf. exact (False_ind _ Hf).
    - exact sc_schedulable_by_on.
  Qed.

End SchedulableExample.
