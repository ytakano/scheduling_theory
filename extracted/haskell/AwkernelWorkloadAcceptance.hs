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

data AwkernelSchedTraceEntry =
   MkAwkernelSchedTraceEntry CPU OpEvent (Option JobId) (List JobId) 
 Bool (Option JobId)

aste_cpu :: AwkernelSchedTraceEntry -> CPU
aste_cpu a =
  case a of {
   MkAwkernelSchedTraceEntry aste_cpu0 _ _ _ _ _ -> aste_cpu0}

aste_event :: AwkernelSchedTraceEntry -> OpEvent
aste_event a =
  case a of {
   MkAwkernelSchedTraceEntry _ aste_event0 _ _ _ _ -> aste_event0}

aste_current :: AwkernelSchedTraceEntry -> Option JobId
aste_current a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ aste_current0 _ _ _ -> aste_current0}

aste_runnable :: AwkernelSchedTraceEntry -> List JobId
aste_runnable a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ aste_runnable0 _ _ -> aste_runnable0}

aste_need_resched :: AwkernelSchedTraceEntry -> Bool
aste_need_resched a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ aste_need_resched0 _ ->
    aste_need_resched0}

aste_dispatch_target :: AwkernelSchedTraceEntry -> Option JobId
aste_dispatch_target a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ _ aste_dispatch_target0 ->
    aste_dispatch_target0}

data AwkernelTaskTraceKind =
   LkSpawn
 | LkRunnable
 | LkChoose
 | LkDispatch
 | LkSleep
 | LkJoinWait
 | LkComplete

data AwkernelTaskTraceEntry =
   MkAwkernelTaskTraceEntry AwkernelTaskTraceKind JobId (Option JobId)

atte_kind :: AwkernelTaskTraceEntry -> AwkernelTaskTraceKind
atte_kind a =
  case a of {
   MkAwkernelTaskTraceEntry atte_kind0 _ _ -> atte_kind0}

atte_subject :: AwkernelTaskTraceEntry -> JobId
atte_subject a =
  case a of {
   MkAwkernelTaskTraceEntry _ atte_subject0 _ -> atte_subject0}

atte_related :: AwkernelTaskTraceEntry -> Option JobId
atte_related a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ atte_related0 -> atte_related0}

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

sched_trace_event_is_wakeup :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_event_is_wakeup j entry =
  case aste_event entry of {
   EvWakeup j' -> eqb0 j' j;
   _ -> False}

sched_trace_event_is_choose :: JobId -> JobId -> AwkernelSchedTraceEntry ->
                               Bool
sched_trace_event_is_choose cpu j entry =
  case aste_event entry of {
   EvChoose c' j' -> andb (eqb0 c' cpu) (eqb0 j' j);
   _ -> False}

sched_trace_event_is_dispatch :: JobId -> JobId -> AwkernelSchedTraceEntry ->
                                 Bool
sched_trace_event_is_dispatch cpu j entry =
  case aste_event entry of {
   EvDispatch c' j' -> andb (eqb0 c' cpu) (eqb0 j' j);
   _ -> False}

sched_trace_event_is_complete :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_event_is_complete j entry =
  case aste_event entry of {
   EvComplete j' -> eqb0 j' j;
   _ -> False}

sched_trace_event_is_stutter :: AwkernelSchedTraceEntry -> Bool
sched_trace_event_is_stutter entry =
  case aste_event entry of {
   EvStutter -> True;
   _ -> False}

sched_trace_is_wakeup :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_wakeup j entry =
  andb
    (andb
      (andb
        (andb
          (andb (eqb0 (aste_cpu entry) O)
            (sched_trace_event_is_wakeup j entry))
          (bool_of_option_none (aste_current entry)))
        (job_list_contains j (aste_runnable entry)))
      (eqb (aste_need_resched entry) False))
    (bool_of_option_none (aste_dispatch_target entry))

sched_trace_is_choose :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_choose j entry =
  andb
    (andb
      (andb
        (andb
          (andb (eqb0 (aste_cpu entry) (S O))
            (sched_trace_event_is_choose (S O) j entry))
          (bool_of_option_none (aste_current entry)))
        (job_list_contains j (aste_runnable entry)))
      (eqb (aste_need_resched entry) False))
    (option_job_eqb (aste_dispatch_target entry) (Some j))

sched_trace_is_dispatch :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_dispatch j entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_dispatch (S O) j entry))
        (option_job_eqb (aste_current entry) (Some j)))
      (eqb (aste_need_resched entry) False))
    (bool_of_option_none (aste_dispatch_target entry))

sched_trace_is_complete :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_complete j entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_complete j entry))
        (bool_of_option_none (aste_current entry)))
      (eqb (aste_need_resched entry) True))
    (bool_of_option_none (aste_dispatch_target entry))

sched_trace_is_stutter :: AwkernelSchedTraceEntry -> Bool
sched_trace_is_stutter entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_stutter entry))
        (bool_of_option_none (aste_current entry)))
      (eqb (aste_need_resched entry) False))
    (bool_of_option_none (aste_dispatch_target entry))

data AwkernelTaskTraceSummary =
   MkAwkernelTaskTraceSummary (Option JobId) (List JobId) (List
                                                          (Prod JobId JobId))

atts_root_task :: AwkernelTaskTraceSummary -> Option JobId
atts_root_task a =
  case a of {
   MkAwkernelTaskTraceSummary atts_root_task0 _ _ -> atts_root_task0}

atts_known_tasks :: AwkernelTaskTraceSummary -> List JobId
atts_known_tasks a =
  case a of {
   MkAwkernelTaskTraceSummary _ atts_known_tasks0 _ -> atts_known_tasks0}

atts_completion_deps :: AwkernelTaskTraceSummary -> List (Prod JobId JobId)
atts_completion_deps a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ atts_completion_deps0 ->
    atts_completion_deps0}

initial_task_trace_summary :: AwkernelTaskTraceSummary
initial_task_trace_summary =
  MkAwkernelTaskTraceSummary None Nil Nil

task_trace_entry_valid :: AwkernelTaskTraceSummary -> AwkernelTaskTraceEntry
                          -> Bool
task_trace_entry_valid summary entry =
  case atte_kind entry of {
   LkSpawn ->
    andb
      (negb
        (job_list_contains (atte_subject entry) (atts_known_tasks summary)))
      (case atte_related entry of {
        Some parent -> job_list_contains parent (atts_known_tasks summary);
        None -> option_job_eqb (atts_root_task summary) None});
   LkJoinWait ->
    case atte_related entry of {
     Some child ->
      andb
        (job_list_contains (atte_subject entry) (atts_known_tasks summary))
        (job_list_contains child (atts_known_tasks summary));
     None -> False};
   _ -> job_list_contains (atte_subject entry) (atts_known_tasks summary)}

task_trace_entry_step :: AwkernelTaskTraceSummary -> AwkernelTaskTraceEntry
                         -> AwkernelTaskTraceSummary
task_trace_entry_step summary entry =
  case atte_kind entry of {
   LkSpawn -> MkAwkernelTaskTraceSummary
    (case atte_related entry of {
      Some _ -> atts_root_task summary;
      None -> Some (atte_subject entry)})
    (add_job_once (atte_subject entry) (atts_known_tasks summary))
    (atts_completion_deps summary);
   LkJoinWait ->
    case atte_related entry of {
     Some child -> MkAwkernelTaskTraceSummary (atts_root_task summary)
      (atts_known_tasks summary)
      (add_pair_once (Pair (atte_subject entry) child)
        (atts_completion_deps summary));
     None -> summary};
   _ -> summary}

summarize_task_trace :: AwkernelTaskTraceSummary -> (List
                        AwkernelTaskTraceEntry) -> Option
                        AwkernelTaskTraceSummary
summarize_task_trace summary task_trace =
  case task_trace of {
   Nil -> Some summary;
   Cons entry task_trace' ->
    case task_trace_entry_valid summary entry of {
     True ->
      summarize_task_trace (task_trace_entry_step summary entry) task_trace';
     False -> None}}

data AwkernelSchedTraceAcceptanceState =
   MkAwkernelSchedTraceAcceptanceState Bool (Option JobId) (List JobId) 
 (List JobId)

astas_started :: AwkernelSchedTraceAcceptanceState -> Bool
astas_started a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState astas_started0 _ _ _ -> astas_started0}

astas_selected :: AwkernelSchedTraceAcceptanceState -> Option JobId
astas_selected a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ astas_selected0 _ _ ->
    astas_selected0}

astas_dispatched :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_dispatched a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ astas_dispatched0 _ ->
    astas_dispatched0}

astas_completed :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_completed a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ astas_completed0 ->
    astas_completed0}

initial_sched_trace_acceptance_state :: AwkernelSchedTraceAcceptanceState
initial_sched_trace_acceptance_state =
  MkAwkernelSchedTraceAcceptanceState False None Nil Nil

sched_trace_step_start :: AwkernelTaskTraceSummary -> AwkernelSchedTraceEntry
                          -> Option AwkernelSchedTraceAcceptanceState
sched_trace_step_start summary entry =
  case atts_root_task summary of {
   Some root ->
    case sched_trace_is_wakeup root entry of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None Nil Nil);
     False -> None};
   None -> None}

sched_trace_step_after_start :: AwkernelTaskTraceSummary ->
                                AwkernelSchedTraceAcceptanceState ->
                                AwkernelSchedTraceEntry -> Option
                                AwkernelSchedTraceAcceptanceState
sched_trace_step_after_start summary st entry =
  let {known = atts_known_tasks summary} in
  let {deps = atts_completion_deps summary} in
  let {
   try_wakeup_job = \j ->
    case andb
           (andb (sched_trace_is_wakeup j entry) (job_list_contains j known))
           (negb (job_list_contains j (astas_completed st))) of {
     True -> Some st;
     False -> None}}
  in
  let {
   try_choose_job = \j ->
    case andb
           (andb
             (andb (sched_trace_is_choose j entry)
               (job_list_contains j known))
             (negb (job_list_contains j (astas_completed st))))
           (option_job_eqb (astas_selected st) None) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True (Some j)
      (astas_dispatched st) (astas_completed st));
     False -> None}}
  in
  let {
   try_dispatch_job = \j ->
    case andb (sched_trace_is_dispatch j entry)
           (option_job_eqb (astas_selected st) (Some j)) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None
      (add_job_once j (astas_dispatched st)) (astas_completed st));
     False -> None}}
  in
  let {
   try_complete_job = \j ->
    case andb
           (andb
             (andb (sched_trace_is_complete j entry)
               (job_list_contains j (astas_dispatched st)))
             (negb (job_list_contains j (astas_completed st))))
           (all_dependencies_completed j deps (astas_completed st)) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None
      (astas_dispatched st) (add_job_once j (astas_completed st)));
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
  case sched_trace_is_stutter entry of {
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

sched_trace_step :: AwkernelTaskTraceSummary ->
                    AwkernelSchedTraceAcceptanceState ->
                    AwkernelSchedTraceEntry -> Option
                    AwkernelSchedTraceAcceptanceState
sched_trace_step summary st entry =
  case astas_started st of {
   True -> sched_trace_step_after_start summary st entry;
   False -> sched_trace_step_start summary entry}

accept_sched_trace_from :: AwkernelTaskTraceSummary ->
                           AwkernelSchedTraceAcceptanceState -> (List
                           AwkernelSchedTraceEntry) -> Bool
accept_sched_trace_from summary st sched_trace =
  case sched_trace of {
   Nil ->
    case atts_root_task summary of {
     Some root -> job_list_contains root (astas_completed st);
     None -> False};
   Cons entry sched_trace' ->
    case sched_trace_step summary st entry of {
     Some st' -> accept_sched_trace_from summary st' sched_trace';
     None -> False}}

sched_trace_family_member :: AwkernelTaskTraceSummary -> (List
                             AwkernelSchedTraceEntry) -> Bool
sched_trace_family_member summary sched_trace =
  accept_sched_trace_from summary initial_sched_trace_acceptance_state
    sched_trace

awk_workload_accepts_sched_trace :: (List AwkernelTaskTraceEntry) -> (List
                                    AwkernelSchedTraceEntry) -> Bool
awk_workload_accepts_sched_trace task_trace sched_trace =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary -> sched_trace_family_member summary sched_trace;
   None -> False}

