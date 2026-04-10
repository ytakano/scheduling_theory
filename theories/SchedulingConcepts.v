From Stdlib Require Import Arith.
Require Import Base.
Require Import ScheduleModel.
Require Import SchedulerInterface.
Require Import SchedulingAlgorithmInterface.

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
