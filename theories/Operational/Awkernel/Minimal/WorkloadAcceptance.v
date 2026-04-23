From Stdlib Require Import List Bool Arith Arith.PeanoNat.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Operational.Common.Step.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
Import ListNotations.

Inductive TaskLifecycleKind : Type :=
| LkSpawn
| LkRunnable
| LkChoose
| LkDispatch
| LkSleep
| LkJoinWait
| LkComplete.

Record TaskLifecycleRecord : Type := mkTaskLifecycleRecord {
  tlr_kind : TaskLifecycleKind;
  tlr_subject : JobId;
  tlr_related : option JobId;
}.

Definition option_job_eqb (x y : option JobId) : bool :=
  match x, y with
  | Some j1, Some j2 => Nat.eqb j1 j2
  | None, None => true
  | _, _ => false
  end.

Fixpoint job_list_contains (j : JobId) (xs : list JobId) : bool :=
  match xs with
  | [] => false
  | x :: xs' => Nat.eqb x j || job_list_contains j xs'
  end.

Fixpoint insert_job_sorted (j : JobId) (xs : list JobId) : list JobId :=
  match xs with
  | [] => [j]
  | x :: xs' =>
      if Nat.eqb j x then x :: xs'
      else if Nat.leb j x then j :: x :: xs'
      else x :: insert_job_sorted j xs'
  end.

Definition add_job_once (j : JobId) (xs : list JobId) : list JobId :=
  insert_job_sorted j xs.

Fixpoint pair_list_contains (x : JobId * JobId) (xs : list (JobId * JobId)) : bool :=
  match xs with
  | [] => false
  | (a, b) :: xs' =>
      let '(x1, x2) := x in
      (Nat.eqb a x1 && Nat.eqb b x2) || pair_list_contains x xs'
  end.

Definition add_pair_once (x : JobId * JobId) (xs : list (JobId * JobId))
    : list (JobId * JobId) :=
  if pair_list_contains x xs then xs else x :: xs.

Fixpoint all_dependencies_completed
    (task_id : JobId)
    (deps : list (JobId * JobId))
    (completed : list JobId) : bool :=
  match deps with
  | [] => true
  | (waiter, child) :: deps' =>
      if Nat.eqb waiter task_id
      then job_list_contains child completed &&
           all_dependencies_completed task_id deps' completed
      else all_dependencies_completed task_id deps' completed
  end.

Definition bool_of_option_none (oj : option JobId) : bool :=
  match oj with
  | Some _ => false
  | None => true
  end.

Definition row_event_is_wakeup (j : JobId) (row : AwkernelCapturedRow) : bool :=
  match acr_event row with
  | EvWakeup j' => Nat.eqb j' j
  | _ => false
  end.

Definition row_event_is_choose (cpu j : JobId) (row : AwkernelCapturedRow) : bool :=
  match acr_event row with
  | EvChoose c' j' => Nat.eqb c' cpu && Nat.eqb j' j
  | _ => false
  end.

Definition row_event_is_dispatch (cpu j : JobId) (row : AwkernelCapturedRow) : bool :=
  match acr_event row with
  | EvDispatch c' j' => Nat.eqb c' cpu && Nat.eqb j' j
  | _ => false
  end.

Definition row_event_is_complete (j : JobId) (row : AwkernelCapturedRow) : bool :=
  match acr_event row with
  | EvComplete j' => Nat.eqb j' j
  | _ => false
  end.

Definition row_event_is_stutter (row : AwkernelCapturedRow) : bool :=
  match acr_event row with
  | EvStutter => true
  | _ => false
  end.

Definition row_is_wakeup (j : JobId) (row : AwkernelCapturedRow) : bool :=
  Nat.eqb (acr_cpu row) 0 &&
  row_event_is_wakeup j row &&
  bool_of_option_none (acr_current row) &&
  job_list_contains j (acr_runnable row) &&
  Bool.eqb (acr_need_resched row) false &&
  bool_of_option_none (acr_dispatch_target row).

Definition row_is_choose (j : JobId) (row : AwkernelCapturedRow) : bool :=
  Nat.eqb (acr_cpu row) 1 &&
  row_event_is_choose 1 j row &&
  bool_of_option_none (acr_current row) &&
  job_list_contains j (acr_runnable row) &&
  Bool.eqb (acr_need_resched row) false &&
  option_job_eqb (acr_dispatch_target row) (Some j).

Definition row_is_dispatch (j : JobId) (row : AwkernelCapturedRow) : bool :=
  Nat.eqb (acr_cpu row) 1 &&
  row_event_is_dispatch 1 j row &&
  option_job_eqb (acr_current row) (Some j) &&
  Bool.eqb (acr_need_resched row) false &&
  bool_of_option_none (acr_dispatch_target row).

Definition row_is_complete (j : JobId) (row : AwkernelCapturedRow) : bool :=
  Nat.eqb (acr_cpu row) 1 &&
  row_event_is_complete j row &&
  bool_of_option_none (acr_current row) &&
  Bool.eqb (acr_need_resched row) true &&
  bool_of_option_none (acr_dispatch_target row).

Definition row_is_stutter (row : AwkernelCapturedRow) : bool :=
  Nat.eqb (acr_cpu row) 1 &&
  row_event_is_stutter row &&
  bool_of_option_none (acr_current row) &&
  Bool.eqb (acr_need_resched row) false &&
  bool_of_option_none (acr_dispatch_target row).

Record WorkloadLifecycleSummary : Type := mkWorkloadLifecycleSummary {
  wls_root_task : option JobId;
  wls_known_tasks : list JobId;
  wls_completion_deps : list (JobId * JobId);
}.

Definition initial_lifecycle_summary : WorkloadLifecycleSummary :=
  mkWorkloadLifecycleSummary None [] [].

Definition lifecycle_record_valid
    (summary : WorkloadLifecycleSummary)
    (rec : TaskLifecycleRecord) : bool :=
  match tlr_kind rec with
  | LkSpawn =>
      negb (job_list_contains (tlr_subject rec) (wls_known_tasks summary)) &&
      match tlr_related rec with
      | None => option_job_eqb (wls_root_task summary) None
      | Some parent => job_list_contains parent (wls_known_tasks summary)
      end
  | LkJoinWait =>
      match tlr_related rec with
      | Some child =>
          job_list_contains (tlr_subject rec) (wls_known_tasks summary) &&
          job_list_contains child (wls_known_tasks summary)
      | None => false
      end
  | _ => job_list_contains (tlr_subject rec) (wls_known_tasks summary)
  end.

Definition lifecycle_record_step
    (summary : WorkloadLifecycleSummary)
    (rec : TaskLifecycleRecord) : WorkloadLifecycleSummary :=
  match tlr_kind rec with
  | LkSpawn =>
      mkWorkloadLifecycleSummary
        (match tlr_related rec with
         | None => Some (tlr_subject rec)
         | Some _ => wls_root_task summary
         end)
        (add_job_once (tlr_subject rec) (wls_known_tasks summary))
        (wls_completion_deps summary)
  | LkJoinWait =>
      match tlr_related rec with
      | Some child =>
          mkWorkloadLifecycleSummary
            (wls_root_task summary)
            (wls_known_tasks summary)
            (add_pair_once (tlr_subject rec, child) (wls_completion_deps summary))
      | None => summary
      end
  | _ => summary
  end.

Fixpoint summarize_lifecycle
    (summary : WorkloadLifecycleSummary)
    (lifecycle : list TaskLifecycleRecord)
    : option WorkloadLifecycleSummary :=
  match lifecycle with
  | [] => Some summary
  | rec :: lifecycle' =>
      if lifecycle_record_valid summary rec
      then summarize_lifecycle (lifecycle_record_step summary rec) lifecycle'
      else None
  end.

Definition workload_lifecycle_well_formed
    (lifecycle : list TaskLifecycleRecord) : bool :=
  match summarize_lifecycle initial_lifecycle_summary lifecycle with
  | Some _ => true
  | None => false
  end.

Record WorkloadRowState : Type := mkWorkloadRowState {
  wrs_started : bool;
  wrs_selected : option JobId;
  wrs_dispatched : list JobId;
  wrs_completed : list JobId;
}.

Definition initial_row_state : WorkloadRowState :=
  mkWorkloadRowState false None [] [].

Definition row_step_start
    (summary : WorkloadLifecycleSummary)
    (row : AwkernelCapturedRow) : option WorkloadRowState :=
  match wls_root_task summary with
  | Some root =>
      if row_is_wakeup root row
      then Some (mkWorkloadRowState true None [] [])
      else None
  | None => None
  end.

Definition row_step_after_start
    (summary : WorkloadLifecycleSummary)
    (st : WorkloadRowState)
    (row : AwkernelCapturedRow) : option WorkloadRowState :=
  let known := wls_known_tasks summary in
  let deps := wls_completion_deps summary in
  let try_wakeup_job (j : JobId) :=
      if row_is_wakeup j row &&
         job_list_contains j known &&
         negb (job_list_contains j (wrs_completed st))
      then Some st
      else None in
  let try_choose_job (j : JobId) :=
      if row_is_choose j row &&
         job_list_contains j known &&
         negb (job_list_contains j (wrs_completed st)) &&
         option_job_eqb (wrs_selected st) None
      then Some (mkWorkloadRowState true (Some j) (wrs_dispatched st) (wrs_completed st))
      else None in
  let try_dispatch_job (j : JobId) :=
      if row_is_dispatch j row &&
         option_job_eqb (wrs_selected st) (Some j)
      then Some (mkWorkloadRowState true None (add_job_once j (wrs_dispatched st)) (wrs_completed st))
      else None in
  let try_complete_job (j : JobId) :=
      if row_is_complete j row &&
         job_list_contains j (wrs_dispatched st) &&
         negb (job_list_contains j (wrs_completed st)) &&
         all_dependencies_completed j deps (wrs_completed st)
      then Some (mkWorkloadRowState true None (wrs_dispatched st) (add_job_once j (wrs_completed st)))
      else None in
  let fix try_known_jobs
      (f : JobId -> option WorkloadRowState)
      (jobs : list JobId) : option WorkloadRowState :=
      match jobs with
      | [] => None
      | j :: jobs' =>
          match f j with
          | Some st' => Some st'
          | None => try_known_jobs f jobs'
          end
      end in
  if row_is_stutter row
  then Some st
  else match try_known_jobs try_wakeup_job known with
       | Some st' => Some st'
       | None =>
           match try_known_jobs try_choose_job known with
           | Some st' => Some st'
           | None =>
               match try_known_jobs try_dispatch_job known with
               | Some st' => Some st'
               | None => try_known_jobs try_complete_job known
               end
           end
       end.

Definition row_step
    (summary : WorkloadLifecycleSummary)
    (st : WorkloadRowState)
    (row : AwkernelCapturedRow) : option WorkloadRowState :=
  if wrs_started st
  then row_step_after_start summary st row
  else row_step_start summary row.

Fixpoint accept_rows_from
    (summary : WorkloadLifecycleSummary)
    (st : WorkloadRowState)
    (rows : list AwkernelCapturedRow) : bool :=
  match rows with
  | [] =>
      match wls_root_task summary with
      | Some root => job_list_contains root (wrs_completed st)
      | None => false
      end
  | row :: rows' =>
      match row_step summary st row with
      | Some st' => accept_rows_from summary st' rows'
      | None => false
      end
  end.

Definition workload_row_family_member
    (summary : WorkloadLifecycleSummary)
    (rows : list AwkernelCapturedRow) : bool :=
  accept_rows_from summary initial_row_state rows.

Definition awk_workload_accepts_trace
    (lifecycle : list TaskLifecycleRecord)
    (rows : list AwkernelCapturedRow) : bool :=
  match summarize_lifecycle initial_lifecycle_summary lifecycle with
  | Some summary => workload_row_family_member summary rows
  | None => false
  end.
