From Stdlib Require Import Arith Arith.PeanoNat Lia Bool.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicTasks.
From RocqSched Require Import TaskModels.Periodic.PeriodicInfinite.

Record PeriodicCodec
    (T : TaskId -> Prop)
    (tasks : TaskId -> Task)
    (offset : TaskId -> Time)
    (jobs : JobId -> Job) : Type := mkPeriodicCodec {
  global_periodic_job_id_of : TaskId -> nat -> JobId;

  global_periodic_job_id_of_sound :
    forall τ k,
      T τ ->
      let j := global_periodic_job_id_of τ k in
      job_task (jobs j) = τ /\
      job_index (jobs j) = k /\
      generated_by_periodic_task tasks offset jobs j;

  global_periodic_job_id_of_complete :
    forall j,
      periodic_jobset T tasks offset jobs j ->
      j = global_periodic_job_id_of (job_task (jobs j)) (job_index (jobs j))
}.
