From Stdlib Require Import Arith Arith.PeanoNat Lia Bool ZArith.
From SchedulingTheory Require Import Foundation.Base.
(* Note: Base.pre_release (t < release_time, schedule-independent) is now in scope.
   Schedule.eligible (released AND NOT completed) is the choose condition for
   valid_schedule; running jobs satisfy eligible but NOT ready.
   Schedule.ready (eligible AND NOT running) is the classical ready-queue state. *)

(* ====================================================== *)
(* Core scheduling concepts used throughout the project.  *)
(* ====================================================== *)

(* ===== 1. Schedule =====

   A schedule is the execution timeline produced by a scheduler.
   For each time step t and CPU c, it returns the job running there (if any).

   Schedule itself is defined in ScheduleModel.v as:
     Definition Schedule := Time -> CPU -> option JobId.

   Key predicates on schedules (also in ScheduleModel.v):
     - eligible j t   : job j is released and not yet completed
     - ready j t      : eligible and not currently running
     - valid_schedule : every running job is eligible at that time
     - feasible_schedule_on J : every job in J completes before its deadline *)

(* ===== 2. SchedulingAlgorithm =====

   A scheduling algorithm is an executable local decision procedure:
   given the current context (job map, CPU count, schedule-so-far, time,
   candidate job list), it selects the next job to run (if any).

   GenericSchedulingAlgorithm is defined in SchedulingAlgorithmInterface.v.
   It captures the minimal correctness contract shared by all algorithms:
     - the chosen job is eligible at the current time
     - if an eligible candidate exists, some job is chosen
     - if no candidate is eligible, None is returned
     - the chosen job is always a member of the candidate list

   Concrete algorithms (EDF, FIFO, …) are instances of this interface,
   defined in UniPolicies/EDF.v and UniPolicies/FIFO.v. *)

(* ===== 3. Scheduler =====

   A scheduler is a semantic scheduling object:
   it characterizes which schedules are admitted for a given job set
   and machine size, typically by combining a scheduling algorithm with
   candidate generation, validity conditions, and refinement obligations.

   Scheduler is defined in SchedulerInterface.v as:
     Record Scheduler := mkScheduler { scheduler_rel : ... }.

   The key predicates on schedulers are:
     - schedulable_by S jobs m       : some valid, feasible schedule exists
     - schedulable_by_on J S jobs m  : same, restricted to job set J *)

(* ===== Intended layering =====

   Schedule              = execution result (timeline)
   SchedulingAlgorithm   = local executable choice rule (per-time-step)
   SchedulingAlgorithmSpec = abstract specification the algorithm must satisfy
   Scheduler             = global semantic wrapper:
                             algorithm + CandidateSource
                             + validity conditions
                             + refinement obligations
                             + CPU/machine structure
                             + schedule semantics

   Examples of how concepts map to this layering:
     - EDF, FIFO, RR            → SchedulingAlgorithm
     - EDF min-deadline order,
       FIFO first-eligible order → SchedulingAlgorithmSpec
     - schedulable_by, etc.     → Scheduler predicates              *)


(* ===== Phase 1: Core Definitions ===== *)

(* Bool indicator: is job j running on cpu c at time t? *)
Definition runs_on (sched : Schedule) (j : JobId) (t : Time) (c : CPU) : bool :=
  match sched t c with
  | Some j' => Nat.eqb j' j
  | None    => false
  end.

(* Count CPUs in 0..m-1 running job j at time t *)
Fixpoint cpu_count (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match m with
  | O    => 0
  | S m' => (if runs_on sched j t m' then 1 else 0) + cpu_count m' sched j t
  end.

(* job-level 累積実行量: [0,t) の全 CPU での job j の総実行ステップ数。
   DAG では node ごとの service (service_node) が別途必要になる。
   この定義は job 全体の work を測る service_job として命名する。 *)
Fixpoint service_job (m : nat) (sched : Schedule) (j : JobId) (t : Time) : nat :=
  match t with
  | O    => 0
  | S t' => cpu_count m sched j t' + service_job m sched j t'
  end.

(* `completed jobs m sched j t` means job j has received >= job_cost units of
   service in [0,t).  Equivalently: "completed by the start of time slot t". *)
Definition completed (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  service_job m sched j t >= job_cost (jobs j).

(* A job is running at time t on some valid CPU in 0..m-1. *)
Definition running (m : nat) (sched : Schedule) (j : JobId) (t : Time) : Prop :=
  exists c : CPU, c < m /\ sched t c = Some j.

(* A job is eligible: released and not yet completed.
   This is the minimum condition for CPU assignment; running jobs satisfy
   eligible. valid_schedule is stated in terms of eligible, not ready,
   because a running job is eligible but NOT ready (ready requires
   NOT running). Zero-cost jobs are immediately completed at t=0 and thus
   never eligible; use valid_jobs to exclude them when needed. *)
Definition eligible (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  released jobs j t /\ ~completed jobs m sched j t.

(* A job is ready: eligible AND not currently executing on any CPU.
   This is the classical "ready queue" state: a job waiting to be scheduled.
   Contrast with eligible, which covers both running and waiting jobs.
   Future DAG extensions will refine this to: eligible AND all predecessors
   completed AND not running. *)
Definition ready (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Prop :=
  eligible jobs m sched j t /\ ~running m sched j t.

(* Sequential-job 仮定: 同じ job は同時に複数 CPU で走らない。
   DAG job ではこの制約は job 単位ではなく node 単位になる:
     - 同じ node は同時に複数 CPU で走らない
     - 同じ job の異なる ready node は別 CPU で同時に走ってよい
   DAG 導入時にはこの定義を node-level に置き換える。 *)
Definition sequential_jobs (m : nat) (sched : Schedule) : Prop :=
  forall j t c1 c2,
    c1 < m -> c2 < m ->
    sched t c1 = Some j -> sched t c2 = Some j -> c1 = c2.

(* A schedule is valid if every scheduled job is eligible at that time.
   This subsumes: no running before release, no running after completion.
   Note: scheduled (running) jobs satisfy eligible (released AND NOT completed)
   but NOT ready (ready additionally requires NOT running), so
   valid_schedule is expressed in terms of eligible, not ready. *)
Definition valid_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j t c, c < m -> sched t c = Some j -> eligible jobs m sched j t.

(* A job misses its deadline if it is not completed by job_abs_deadline. *)
Definition missed_deadline (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) : Prop :=
  ~completed jobs m sched j (job_abs_deadline (jobs j)).

(* A schedule is feasible if no job misses its deadline.
   Total-function version: quantifies over all JobId. *)
Definition feasible_schedule (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, ~missed_deadline jobs m sched j.

(* A job set is feasible if there exists a valid, feasible schedule.
   Total-function version: quantifies over all JobId.
   For finite/subset reasoning, use feasible_on. *)
Definition feasible (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched, valid_schedule jobs m sched /\ feasible_schedule jobs m sched.

(* Restrict feasibility to a designated job set J.
   This is a forward-compatible layer for moving from the current
   total-function model to finite job-set reasoning. *)
Definition feasible_schedule_on (J : JobId -> Prop)
    (jobs : JobId -> Job) (m : nat) (sched : Schedule) : Prop :=
  forall j, J j -> ~missed_deadline jobs m sched j.

Definition feasible_on (J : JobId -> Prop)
    (jobs : JobId -> Job) (m : nat) : Prop :=
  exists sched, valid_schedule jobs m sched /\ feasible_schedule_on J jobs m sched.

(* ===== Phase 2: Laxity Definitions ===== *)

(* Remaining work for job j at time t: job_cost minus cumulative service.
   Uses Nat.sub, so the result is floored at 0 once the job has completed. *)
Definition remaining_cost
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : nat :=
  job_cost (jobs j) - service_job m sched j t.

(* Laxity (slack) of job j at time t: how much time remains before the job
   must run continuously without preemption to meet its deadline.
   Uses Z so that negative laxity (overdue / deadline miss) is representable. *)
Definition laxity
    (jobs : JobId -> Job) (m : nat) (sched : Schedule)
    (j : JobId) (t : Time) : Z :=
  Z.of_nat (job_abs_deadline (jobs j))
  - Z.of_nat t
  - Z.of_nat (remaining_cost jobs m sched j t).

