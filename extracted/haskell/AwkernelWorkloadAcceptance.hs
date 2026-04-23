module AwkernelWorkloadAcceptance where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

eqb0 :: Nat -> Nat -> Bool
eqb0 n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb0 n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

type JobId = Nat

type CPU = Nat

data OpEvent =
   EvWakeup JobId
 | EvBlock JobId
 | EvComplete JobId
 | EvRequestResched CPU
 | EvHandleResched CPU
 | EvChoose CPU JobId
 | EvDispatch CPU JobId
 | EvPreempt CPU JobId JobId
 | EvStutter
 | EvTick

data AwkernelCapturedRow =
   MkAwkernelCapturedRow CPU OpEvent (Option JobId) (List JobId) Bool 
 (Option JobId)

acr_cpu :: AwkernelCapturedRow -> CPU
acr_cpu a =
  case a of {
   MkAwkernelCapturedRow acr_cpu0 _ _ _ _ _ -> acr_cpu0}

acr_event :: AwkernelCapturedRow -> OpEvent
acr_event a =
  case a of {
   MkAwkernelCapturedRow _ acr_event0 _ _ _ _ -> acr_event0}

acr_current :: AwkernelCapturedRow -> Option JobId
acr_current a =
  case a of {
   MkAwkernelCapturedRow _ _ acr_current0 _ _ _ -> acr_current0}

acr_runnable :: AwkernelCapturedRow -> List JobId
acr_runnable a =
  case a of {
   MkAwkernelCapturedRow _ _ _ acr_runnable0 _ _ -> acr_runnable0}

acr_need_resched :: AwkernelCapturedRow -> Bool
acr_need_resched a =
  case a of {
   MkAwkernelCapturedRow _ _ _ _ acr_need_resched0 _ -> acr_need_resched0}

acr_dispatch_target :: AwkernelCapturedRow -> Option JobId
acr_dispatch_target a =
  case a of {
   MkAwkernelCapturedRow _ _ _ _ _ acr_dispatch_target0 ->
    acr_dispatch_target0}

data TaskLifecycleKind =
   LkSpawn
 | LkRunnable
 | LkChoose
 | LkDispatch
 | LkSleep
 | LkJoinWait
 | LkComplete

data TaskLifecycleRecord =
   MkTaskLifecycleRecord TaskLifecycleKind JobId (Option JobId)

tlr_kind :: TaskLifecycleRecord -> TaskLifecycleKind
tlr_kind t =
  case t of {
   MkTaskLifecycleRecord tlr_kind0 _ _ -> tlr_kind0}

tlr_subject :: TaskLifecycleRecord -> JobId
tlr_subject t =
  case t of {
   MkTaskLifecycleRecord _ tlr_subject0 _ -> tlr_subject0}

tlr_related :: TaskLifecycleRecord -> Option JobId
tlr_related t =
  case t of {
   MkTaskLifecycleRecord _ _ tlr_related0 -> tlr_related0}

option_job_eqb :: (Option JobId) -> (Option JobId) -> Bool
option_job_eqb x y =
  case x of {
   Some j1 -> case y of {
               Some j2 -> eqb0 j1 j2;
               None -> False};
   None -> case y of {
            Some _ -> False;
            None -> True}}

job_list_contains :: JobId -> (List JobId) -> Bool
job_list_contains j xs =
  case xs of {
   Nil -> False;
   Cons x xs' -> orb (eqb0 x j) (job_list_contains j xs')}

insert_job_sorted :: JobId -> (List JobId) -> List JobId
insert_job_sorted j xs =
  case xs of {
   Nil -> Cons j Nil;
   Cons x xs' ->
    case eqb0 j x of {
     True -> Cons x xs';
     False ->
      case leb j x of {
       True -> Cons j (Cons x xs');
       False -> Cons x (insert_job_sorted j xs')}}}

add_job_once :: JobId -> (List JobId) -> List JobId
add_job_once =
  insert_job_sorted

pair_list_contains :: (Prod JobId JobId) -> (List (Prod JobId JobId)) -> Bool
pair_list_contains x xs =
  case xs of {
   Nil -> False;
   Cons p xs' ->
    case p of {
     Pair a b ->
      case x of {
       Pair x1 x2 ->
        orb (andb (eqb0 a x1) (eqb0 b x2)) (pair_list_contains x xs')}}}

add_pair_once :: (Prod JobId JobId) -> (List (Prod JobId JobId)) -> List
                 (Prod JobId JobId)
add_pair_once x xs =
  case pair_list_contains x xs of {
   True -> xs;
   False -> Cons x xs}

all_dependencies_completed :: JobId -> (List (Prod JobId JobId)) -> (List
                              JobId) -> Bool
all_dependencies_completed task_id deps completed =
  case deps of {
   Nil -> True;
   Cons p deps' ->
    case p of {
     Pair waiter child ->
      case eqb0 waiter task_id of {
       True ->
        andb (job_list_contains child completed)
          (all_dependencies_completed task_id deps' completed);
       False -> all_dependencies_completed task_id deps' completed}}}

bool_of_option_none :: (Option JobId) -> Bool
bool_of_option_none oj =
  case oj of {
   Some _ -> False;
   None -> True}

row_event_is_wakeup :: JobId -> AwkernelCapturedRow -> Bool
row_event_is_wakeup j row =
  case acr_event row of {
   EvWakeup j' -> eqb0 j' j;
   _ -> False}

row_event_is_choose :: JobId -> JobId -> AwkernelCapturedRow -> Bool
row_event_is_choose cpu j row =
  case acr_event row of {
   EvChoose c' j' -> andb (eqb0 c' cpu) (eqb0 j' j);
   _ -> False}

row_event_is_dispatch :: JobId -> JobId -> AwkernelCapturedRow -> Bool
row_event_is_dispatch cpu j row =
  case acr_event row of {
   EvDispatch c' j' -> andb (eqb0 c' cpu) (eqb0 j' j);
   _ -> False}

row_event_is_complete :: JobId -> AwkernelCapturedRow -> Bool
row_event_is_complete j row =
  case acr_event row of {
   EvComplete j' -> eqb0 j' j;
   _ -> False}

row_event_is_stutter :: AwkernelCapturedRow -> Bool
row_event_is_stutter row =
  case acr_event row of {
   EvStutter -> True;
   _ -> False}

row_is_wakeup :: JobId -> AwkernelCapturedRow -> Bool
row_is_wakeup j row =
  andb
    (andb
      (andb
        (andb (andb (eqb0 (acr_cpu row) O) (row_event_is_wakeup j row))
          (bool_of_option_none (acr_current row)))
        (job_list_contains j (acr_runnable row)))
      (eqb (acr_need_resched row) False))
    (bool_of_option_none (acr_dispatch_target row))

row_is_choose :: JobId -> AwkernelCapturedRow -> Bool
row_is_choose j row =
  andb
    (andb
      (andb
        (andb
          (andb (eqb0 (acr_cpu row) (S O)) (row_event_is_choose (S O) j row))
          (bool_of_option_none (acr_current row)))
        (job_list_contains j (acr_runnable row)))
      (eqb (acr_need_resched row) False))
    (option_job_eqb (acr_dispatch_target row) (Some j))

row_is_dispatch :: JobId -> AwkernelCapturedRow -> Bool
row_is_dispatch j row =
  andb
    (andb
      (andb
        (andb (eqb0 (acr_cpu row) (S O)) (row_event_is_dispatch (S O) j row))
        (option_job_eqb (acr_current row) (Some j)))
      (eqb (acr_need_resched row) False))
    (bool_of_option_none (acr_dispatch_target row))

row_is_complete :: JobId -> AwkernelCapturedRow -> Bool
row_is_complete j row =
  andb
    (andb
      (andb (andb (eqb0 (acr_cpu row) (S O)) (row_event_is_complete j row))
        (bool_of_option_none (acr_current row)))
      (eqb (acr_need_resched row) True))
    (bool_of_option_none (acr_dispatch_target row))

row_is_stutter :: AwkernelCapturedRow -> Bool
row_is_stutter row =
  andb
    (andb
      (andb (andb (eqb0 (acr_cpu row) (S O)) (row_event_is_stutter row))
        (bool_of_option_none (acr_current row)))
      (eqb (acr_need_resched row) False))
    (bool_of_option_none (acr_dispatch_target row))

data WorkloadLifecycleSummary =
   MkWorkloadLifecycleSummary (Option JobId) (List JobId) (List
                                                          (Prod JobId JobId))

wls_root_task :: WorkloadLifecycleSummary -> Option JobId
wls_root_task w =
  case w of {
   MkWorkloadLifecycleSummary wls_root_task0 _ _ -> wls_root_task0}

wls_known_tasks :: WorkloadLifecycleSummary -> List JobId
wls_known_tasks w =
  case w of {
   MkWorkloadLifecycleSummary _ wls_known_tasks0 _ -> wls_known_tasks0}

wls_completion_deps :: WorkloadLifecycleSummary -> List (Prod JobId JobId)
wls_completion_deps w =
  case w of {
   MkWorkloadLifecycleSummary _ _ wls_completion_deps0 ->
    wls_completion_deps0}

initial_lifecycle_summary :: WorkloadLifecycleSummary
initial_lifecycle_summary =
  MkWorkloadLifecycleSummary None Nil Nil

lifecycle_record_valid :: WorkloadLifecycleSummary -> TaskLifecycleRecord ->
                          Bool
lifecycle_record_valid summary rec0 =
  case tlr_kind rec0 of {
   LkSpawn ->
    andb
      (negb (job_list_contains (tlr_subject rec0) (wls_known_tasks summary)))
      (case tlr_related rec0 of {
        Some parent -> job_list_contains parent (wls_known_tasks summary);
        None -> option_job_eqb (wls_root_task summary) None});
   LkJoinWait ->
    case tlr_related rec0 of {
     Some child ->
      andb (job_list_contains (tlr_subject rec0) (wls_known_tasks summary))
        (job_list_contains child (wls_known_tasks summary));
     None -> False};
   _ -> job_list_contains (tlr_subject rec0) (wls_known_tasks summary)}

lifecycle_record_step :: WorkloadLifecycleSummary -> TaskLifecycleRecord ->
                         WorkloadLifecycleSummary
lifecycle_record_step summary rec0 =
  case tlr_kind rec0 of {
   LkSpawn -> MkWorkloadLifecycleSummary
    (case tlr_related rec0 of {
      Some _ -> wls_root_task summary;
      None -> Some (tlr_subject rec0)})
    (add_job_once (tlr_subject rec0) (wls_known_tasks summary))
    (wls_completion_deps summary);
   LkJoinWait ->
    case tlr_related rec0 of {
     Some child -> MkWorkloadLifecycleSummary (wls_root_task summary)
      (wls_known_tasks summary)
      (add_pair_once (Pair (tlr_subject rec0) child)
        (wls_completion_deps summary));
     None -> summary};
   _ -> summary}

summarize_lifecycle :: WorkloadLifecycleSummary -> (List TaskLifecycleRecord)
                       -> Option WorkloadLifecycleSummary
summarize_lifecycle summary lifecycle =
  case lifecycle of {
   Nil -> Some summary;
   Cons rec0 lifecycle' ->
    case lifecycle_record_valid summary rec0 of {
     True ->
      summarize_lifecycle (lifecycle_record_step summary rec0) lifecycle';
     False -> None}}

data WorkloadRowState =
   MkWorkloadRowState Bool (Option JobId) (List JobId) (List JobId)

wrs_started :: WorkloadRowState -> Bool
wrs_started w =
  case w of {
   MkWorkloadRowState wrs_started0 _ _ _ -> wrs_started0}

wrs_selected :: WorkloadRowState -> Option JobId
wrs_selected w =
  case w of {
   MkWorkloadRowState _ wrs_selected0 _ _ -> wrs_selected0}

wrs_dispatched :: WorkloadRowState -> List JobId
wrs_dispatched w =
  case w of {
   MkWorkloadRowState _ _ wrs_dispatched0 _ -> wrs_dispatched0}

wrs_completed :: WorkloadRowState -> List JobId
wrs_completed w =
  case w of {
   MkWorkloadRowState _ _ _ wrs_completed0 -> wrs_completed0}

initial_row_state :: WorkloadRowState
initial_row_state =
  MkWorkloadRowState False None Nil Nil

row_step_start :: WorkloadLifecycleSummary -> AwkernelCapturedRow -> Option
                  WorkloadRowState
row_step_start summary row =
  case wls_root_task summary of {
   Some root ->
    case row_is_wakeup root row of {
     True -> Some (MkWorkloadRowState True None Nil Nil);
     False -> None};
   None -> None}

row_step_after_start :: WorkloadLifecycleSummary -> WorkloadRowState ->
                        AwkernelCapturedRow -> Option WorkloadRowState
row_step_after_start summary st row =
  let {known = wls_known_tasks summary} in
  let {deps = wls_completion_deps summary} in
  let {
   try_wakeup_job = \j ->
    case andb (andb (row_is_wakeup j row) (job_list_contains j known))
           (negb (job_list_contains j (wrs_completed st))) of {
     True -> Some st;
     False -> None}}
  in
  let {
   try_choose_job = \j ->
    case andb
           (andb (andb (row_is_choose j row) (job_list_contains j known))
             (negb (job_list_contains j (wrs_completed st))))
           (option_job_eqb (wrs_selected st) None) of {
     True -> Some (MkWorkloadRowState True (Some j) (wrs_dispatched st)
      (wrs_completed st));
     False -> None}}
  in
  let {
   try_dispatch_job = \j ->
    case andb (row_is_dispatch j row)
           (option_job_eqb (wrs_selected st) (Some j)) of {
     True -> Some (MkWorkloadRowState True None
      (add_job_once j (wrs_dispatched st)) (wrs_completed st));
     False -> None}}
  in
  let {
   try_complete_job = \j ->
    case andb
           (andb
             (andb (row_is_complete j row)
               (job_list_contains j (wrs_dispatched st)))
             (negb (job_list_contains j (wrs_completed st))))
           (all_dependencies_completed j deps (wrs_completed st)) of {
     True -> Some (MkWorkloadRowState True None (wrs_dispatched st)
      (add_job_once j (wrs_completed st)));
     False -> None}}
  in
  let {
   try_known_jobs = let {
                     try_known_jobs f jobs =
                       case jobs of {
                        Nil -> None;
                        Cons j jobs' ->
                         case f j of {
                          Some st' -> Some st';
                          None -> try_known_jobs f jobs'}}}
                    in try_known_jobs}
  in
  case row_is_stutter row of {
   True -> Some st;
   False ->
    case try_known_jobs try_wakeup_job known of {
     Some st' -> Some st';
     None ->
      case try_known_jobs try_choose_job known of {
       Some st' -> Some st';
       None ->
        case try_known_jobs try_dispatch_job known of {
         Some st' -> Some st';
         None -> try_known_jobs try_complete_job known}}}}

row_step :: WorkloadLifecycleSummary -> WorkloadRowState ->
            AwkernelCapturedRow -> Option WorkloadRowState
row_step summary st row =
  case wrs_started st of {
   True -> row_step_after_start summary st row;
   False -> row_step_start summary row}

accept_rows_from :: WorkloadLifecycleSummary -> WorkloadRowState -> (List
                    AwkernelCapturedRow) -> Bool
accept_rows_from summary st rows =
  case rows of {
   Nil ->
    case wls_root_task summary of {
     Some root -> job_list_contains root (wrs_completed st);
     None -> False};
   Cons row rows' ->
    case row_step summary st row of {
     Some st' -> accept_rows_from summary st' rows';
     None -> False}}

workload_row_family_member :: WorkloadLifecycleSummary -> (List
                              AwkernelCapturedRow) -> Bool
workload_row_family_member summary rows =
  accept_rows_from summary initial_row_state rows

awk_workload_accepts_trace :: (List TaskLifecycleRecord) -> (List
                              AwkernelCapturedRow) -> Bool
awk_workload_accepts_trace lifecycle rows =
  case summarize_lifecycle initial_lifecycle_summary lifecycle of {
   Some summary -> workload_row_family_member summary rows;
   None -> False}

