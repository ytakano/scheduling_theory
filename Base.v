(* ===== Phase 0: Design Decisions ===== *)

(* === DAG 拡張に向けた設計メモ ===
   将来的には実行単位を 3 層に分ける:
     Task  : 周期的な生成ルール
     Job   : Task の具体的な実行インスタンス
     Node  : Job 内部の並列実行ノード（DAG ノード）

   現在は Node を導入しておらず、実行単位 = Job。
   DAG 導入時には Schedule の型が
     Time -> CPU -> option JobId
   から
     Time -> CPU -> option NodeId  (または option (JobId * NodeId))
   へ移行する可能性がある。

   各定義の DAG 拡張方針は個別のコメントに記載する。 *)

Definition JobId  : Type := nat.
Definition TaskId : Type := nat.
Definition CPU    : Type := nat.
Definition Time   : Type := nat.

(* Task: periodic task as a generation rule for jobs.
   Not yet used in proofs; defined here as a skeleton for future
   periodic scheduling theory (utilization bounds, EDF optimality, etc.). *)
Record Task : Type := mkTask {
  task_cost     : nat;  (* WCET: worst-case execution time per job *)
  task_period   : nat;  (* period: minimum inter-arrival time *)
  task_relative_deadline : nat;  (* relative deadline *)
}.

(* Job: a concrete execution instance, optionally tied to a Task.
   job_task / job_index are unused by current lemmas and may be
   set to 0 for standalone jobs.  They exist so that periodic-task
   extensions can attach identity without restructuring this record. *)
Record Job : Type := mkJob {
  job_task         : TaskId; (* which task generated this job (0 = anonymous) *)
  job_index        : nat;    (* k-th job of that task, 0-indexed (instance number) *)
  job_release      : Time;   (* absolute release time *)
  job_cost         : nat;    (* execution time required by this job *)
  job_abs_deadline : Time;   (* absolute deadline *)
}.

(* time -> CPU -> option JobId: multicore schedule.
   Sequential-job モデルでは実行単位 = job。
   DAG 導入時には option NodeId または option (JobId * NodeId) に移行予定。 *)
Definition Schedule : Type := Time -> CPU -> option JobId.

(* A job has been released at time t *)
Definition released (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  job_release (jobs j) <= t.

(* A job is waiting (pre-release): not yet released at time t.
   This predicate is schedule-independent and depends only on the job's
   release time. Contrast with runnable (released but not completed) in
   Schedule.v. *)
Definition waiting (jobs : JobId -> Job) (j : JobId) (t : Time) : Prop :=
  t < job_release (jobs j).

(* A job set is valid when every job has positive cost.
   Zero-cost jobs are immediately completed at t=0 and thus never waiting/ready.
   This predicate will be used by periodic job generation (Phase 12+):
   e.g. "released directly implies potentially ready" relies on 0 < job_cost. *)
Definition valid_jobs (jobs : JobId -> Job) : Prop :=
  forall j, 0 < job_cost (jobs j).

(* Relationship between Task and Job: a job j belongs to task τ if
   job_task (jobs j) = τ.  Periodic-task constraints (release pattern,
   relative deadline → absolute deadline) will be expressed via
   valid_job_of_task below. *)

(* Important:
   valid_job_of_task is NOT yet a full periodic-generation predicate.
   At this stage, it only expresses local consistency between a job and
   the parameters of its generating task, namely:

   - the absolute deadline is derived from release + relative deadline
   - the job cost is bounded by the task WCET

   Future periodic-task theory should add a separate predicate/function
   for generation rules, e.g.:
     - release = offset + job_index * period
     - monotonicity / non-overlap of generated jobs
     - uniqueness of the k-th job for each task *)
Definition valid_job_of_task (tasks : TaskId -> Task) (jobs : JobId -> Job)
    (j : JobId) : Prop :=
  let τ := job_task (jobs j) in
  job_abs_deadline (jobs j) =
    job_release (jobs j) + task_relative_deadline (tasks τ) /\
  job_cost (jobs j) <= task_cost (tasks τ).
