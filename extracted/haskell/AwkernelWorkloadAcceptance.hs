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

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec o s n =
  case n of {
   O -> o;
   S n0 -> s n0 (nat_rec o s n0)}

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec nil cons l =
  case l of {
   Nil -> nil;
   Cons a l0 -> cons a l0 (list_rec nil cons l0)}

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Sumbool =
   Left
 | Right

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

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

ltb :: Nat -> Nat -> Bool
ltb n m =
  leb (S n) m

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right})
    (\_ iHn m -> case m of {
                  O -> Right;
                  S n0 -> iHn n0})
    n

nth :: Nat -> (List a1) -> a1 -> a1
nth n l default0 =
  case n of {
   O -> case l of {
         Nil -> default0;
         Cons x _ -> x};
   S m -> case l of {
           Nil -> default0;
           Cons _ l' -> nth m l' default0}}

firstn :: Nat -> (List a1) -> List a1
firstn n l =
  case n of {
   O -> Nil;
   S n0 -> case l of {
            Nil -> Nil;
            Cons a l0 -> Cons a (firstn n0 l0)}}

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl ->
    let {s = h a0 a} in case s of {
                         Left -> Left;
                         Right -> iHl})
    l

nth_error :: (List a1) -> Nat -> Option a1
nth_error l n =
  case n of {
   O -> case l of {
         Nil -> None;
         Cons x _ -> Some x};
   S n0 -> case l of {
            Nil -> None;
            Cons _ l' -> nth_error l' n0}}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

nodup :: (a1 -> a1 -> Sumbool) -> (List a1) -> List a1
nodup decA l =
  case l of {
   Nil -> Nil;
   Cons x xs ->
    case in_dec decA x xs of {
     Left -> nodup decA xs;
     Right -> Cons x (nodup decA xs)}}

type JobId = Nat

type TaskId = Nat

type CPU = Nat

type Time = Nat

data Job =
   MkJob TaskId Nat Time Nat Time (Time -> Bool)

job_release :: Job -> Time
job_release j =
  case j of {
   MkJob _ _ job_release0 _ _ _ -> job_release0}

job_cost :: Job -> Nat
job_cost j =
  case j of {
   MkJob _ _ _ job_cost0 _ _ -> job_cost0}

job_blocked :: Job -> Time -> Bool
job_blocked j =
  case j of {
   MkJob _ _ _ _ _ job_blocked0 -> job_blocked0}

type Schedule = Time -> CPU -> Option JobId

data OpEvent =
   EvWakeup JobId
 | EvBlock JobId
 | EvComplete JobId
 | EvJoinTargetReady JobId
 | EvRequestResched CPU
 | EvHandleResched CPU
 | EvChoose CPU JobId
 | EvDispatch CPU JobId
 | EvPreempt CPU JobId JobId
 | EvStutter
 | EvTick

runs_on :: Schedule -> JobId -> Time -> CPU -> Bool
runs_on sched j t c =
  case sched t c of {
   Some j' -> eqb0 j' j;
   None -> False}

cpu_count :: Nat -> Schedule -> JobId -> Time -> Nat
cpu_count m sched j t =
  case m of {
   O -> O;
   S m' ->
    add (case runs_on sched j t m' of {
          True -> S O;
          False -> O})
      (cpu_count m' sched j t)}

service_job :: Nat -> Schedule -> JobId -> Time -> Nat
service_job m sched j t =
  case t of {
   O -> O;
   S t' -> add (cpu_count m sched j t') (service_job m sched j t')}

eligibleb :: (JobId -> Job) -> Nat -> Schedule -> JobId -> Time -> Bool
eligibleb jobs m sched j t =
  andb
    (andb (leb (job_release (jobs j)) t)
      (negb (leb (job_cost (jobs j)) (service_job m sched j t))))
    (negb (job_blocked (jobs j) t))

type GenericTopMSchedulingAlgorithm =
  (JobId -> Job) -> Nat -> Schedule -> Time -> (List JobId) -> List JobId
  -- singleton inductive, whose constructor was mkGenericTopMSchedulingAlgorithm
  
choose_top_m :: GenericTopMSchedulingAlgorithm -> (JobId -> Job) -> Nat ->
                Schedule -> Time -> (List JobId) -> List JobId
choose_top_m g =
  g

data AwkernelSchedTraceEntry =
   MkAwkernelSchedTraceEntry CPU OpEvent (Option JobId) (List JobId) 
 Bool (Option JobId) (List (Option JobId)) (List Bool) (List (Option JobId))

aste_cpu :: AwkernelSchedTraceEntry -> CPU
aste_cpu a =
  case a of {
   MkAwkernelSchedTraceEntry aste_cpu0 _ _ _ _ _ _ _ _ -> aste_cpu0}

aste_event :: AwkernelSchedTraceEntry -> OpEvent
aste_event a =
  case a of {
   MkAwkernelSchedTraceEntry _ aste_event0 _ _ _ _ _ _ _ -> aste_event0}

aste_current :: AwkernelSchedTraceEntry -> Option JobId
aste_current a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ aste_current0 _ _ _ _ _ _ -> aste_current0}

aste_runnable :: AwkernelSchedTraceEntry -> List JobId
aste_runnable a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ aste_runnable0 _ _ _ _ _ -> aste_runnable0}

aste_need_resched :: AwkernelSchedTraceEntry -> Bool
aste_need_resched a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ aste_need_resched0 _ _ _ _ ->
    aste_need_resched0}

aste_dispatch_target :: AwkernelSchedTraceEntry -> Option JobId
aste_dispatch_target a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ _ aste_dispatch_target0 _ _ _ ->
    aste_dispatch_target0}

sched_trace_primary_current :: AwkernelSchedTraceEntry -> Option JobId
sched_trace_primary_current =
  aste_current

sched_trace_primary_need_resched :: AwkernelSchedTraceEntry -> Bool
sched_trace_primary_need_resched =
  aste_need_resched

sched_trace_primary_dispatch_target :: AwkernelSchedTraceEntry -> Option
                                       JobId
sched_trace_primary_dispatch_target =
  aste_dispatch_target

data AwkernelTaskTraceKind =
   LkSpawn
 | LkRunnable
 | LkChoose
 | LkDispatch
 | LkSleep
 | LkJoinWait
 | LkJoinTargetReady
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

first_some :: (a1 -> Option a2) -> (List a1) -> Option a2
first_some f xs =
  case xs of {
   Nil -> None;
   Cons x xs' -> case f x of {
                  Some y -> Some y;
                  None -> first_some f xs'}}

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

all_dependencies_ready :: JobId -> (List (Prod JobId JobId)) -> (List
                          JobId) -> Bool
all_dependencies_ready task_id deps ready_targets =
  case deps of {
   Nil -> True;
   Cons p deps' ->
    case p of {
     Pair waiter target ->
      case eqb0 waiter task_id of {
       True ->
        andb (job_list_contains target ready_targets)
          (all_dependencies_ready task_id deps' ready_targets);
       False -> all_dependencies_ready task_id deps' ready_targets}}}

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

sched_trace_event_is_join_target_ready :: JobId -> AwkernelSchedTraceEntry ->
                                          Bool
sched_trace_event_is_join_target_ready j entry =
  case aste_event entry of {
   EvJoinTargetReady j' -> eqb0 j' j;
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
          (bool_of_option_none (sched_trace_primary_current entry)))
        (job_list_contains j (aste_runnable entry)))
      (eqb (sched_trace_primary_need_resched entry) False))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_choose :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_choose j entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_choose (S O) j entry))
        (bool_of_option_none (sched_trace_primary_current entry)))
      (job_list_contains j (aste_runnable entry)))
    (option_job_eqb (sched_trace_primary_dispatch_target entry) (Some j))

sched_trace_is_dispatch :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_dispatch j entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_dispatch (S O) j entry))
        (option_job_eqb (sched_trace_primary_current entry) (Some j)))
      (eqb (sched_trace_primary_need_resched entry) False))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_complete :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_complete j entry =
  andb
    (andb
      (andb
        (andb (eqb0 (aste_cpu entry) (S O))
          (sched_trace_event_is_complete j entry))
        (bool_of_option_none (sched_trace_primary_current entry)))
      (eqb (sched_trace_primary_need_resched entry) True))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_join_target_ready :: JobId -> AwkernelSchedTraceEntry -> Bool
sched_trace_is_join_target_ready j entry =
  andb (eqb0 (aste_cpu entry) (S O))
    (sched_trace_event_is_join_target_ready j entry)

sched_trace_is_stutter :: AwkernelSchedTraceEntry -> Bool
sched_trace_is_stutter entry =
  andb
    (andb
      (andb (eqb0 (aste_cpu entry) (S O))
        (sched_trace_event_is_stutter entry))
      (bool_of_option_none (sched_trace_primary_current entry)))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

data AwkernelTaskTraceSummary =
   MkAwkernelTaskTraceSummary (Option JobId) (List JobId) (List
                                                          (Prod JobId JobId))
 (List JobId)

atts_root_task :: AwkernelTaskTraceSummary -> Option JobId
atts_root_task a =
  case a of {
   MkAwkernelTaskTraceSummary atts_root_task0 _ _ _ -> atts_root_task0}

atts_known_tasks :: AwkernelTaskTraceSummary -> List JobId
atts_known_tasks a =
  case a of {
   MkAwkernelTaskTraceSummary _ atts_known_tasks0 _ _ -> atts_known_tasks0}

atts_completion_deps :: AwkernelTaskTraceSummary -> List (Prod JobId JobId)
atts_completion_deps a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ atts_completion_deps0 _ ->
    atts_completion_deps0}

atts_ready_targets :: AwkernelTaskTraceSummary -> List JobId
atts_ready_targets a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ atts_ready_targets0 ->
    atts_ready_targets0}

initial_task_trace_summary :: AwkernelTaskTraceSummary
initial_task_trace_summary =
  MkAwkernelTaskTraceSummary None Nil Nil Nil

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
     Some target ->
      andb
        (job_list_contains (atte_subject entry) (atts_known_tasks summary))
        (job_list_contains target (atts_known_tasks summary));
     None -> False};
   LkJoinTargetReady ->
    case atte_related entry of {
     Some _ -> False;
     None ->
      andb
        (job_list_contains (atte_subject entry) (atts_known_tasks summary))
        (negb
          (job_list_contains (atte_subject entry)
            (atts_ready_targets summary)))};
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
    (atts_completion_deps summary) (atts_ready_targets summary);
   LkJoinWait ->
    case atte_related entry of {
     Some target -> MkAwkernelTaskTraceSummary (atts_root_task summary)
      (atts_known_tasks summary)
      (add_pair_once (Pair (atte_subject entry) target)
        (atts_completion_deps summary))
      (atts_ready_targets summary);
     None -> summary};
   LkJoinTargetReady -> MkAwkernelTaskTraceSummary (atts_root_task summary)
    (atts_known_tasks summary) (atts_completion_deps summary)
    (add_job_once (atte_subject entry) (atts_ready_targets summary));
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
 (List JobId) (List JobId)

astas_started :: AwkernelSchedTraceAcceptanceState -> Bool
astas_started a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState astas_started0 _ _ _ _ ->
    astas_started0}

astas_selected :: AwkernelSchedTraceAcceptanceState -> Option JobId
astas_selected a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ astas_selected0 _ _ _ ->
    astas_selected0}

astas_dispatched :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_dispatched a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ astas_dispatched0 _ _ ->
    astas_dispatched0}

astas_completed :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_completed a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ astas_completed0 _ ->
    astas_completed0}

astas_ready_targets :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_ready_targets a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ _ astas_ready_targets0 ->
    astas_ready_targets0}

initial_sched_trace_acceptance_state :: AwkernelSchedTraceAcceptanceState
initial_sched_trace_acceptance_state =
  MkAwkernelSchedTraceAcceptanceState False None Nil Nil Nil

sched_trace_step_start :: AwkernelTaskTraceSummary -> AwkernelSchedTraceEntry
                          -> Option AwkernelSchedTraceAcceptanceState
sched_trace_step_start summary entry =
  case atts_root_task summary of {
   Some root ->
    case sched_trace_is_wakeup root entry of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None Nil Nil Nil);
     False -> None};
   None -> None}

sched_trace_step_after_start :: AwkernelTaskTraceSummary ->
                                AwkernelSchedTraceAcceptanceState ->
                                AwkernelSchedTraceEntry -> Option
                                AwkernelSchedTraceAcceptanceState
sched_trace_step_after_start summary st entry =
  let {known = atts_known_tasks summary} in
  let {deps = atts_completion_deps summary} in
  let {ready_targets = atts_ready_targets summary} in
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
      (astas_dispatched st) (astas_completed st) (astas_ready_targets st));
     False -> None}}
  in
  let {
   try_dispatch_job = \j ->
    case andb (sched_trace_is_dispatch j entry)
           (option_job_eqb (astas_selected st) (Some j)) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None
      (add_job_once j (astas_dispatched st)) (astas_completed st)
      (astas_ready_targets st));
     False -> None}}
  in
  let {
   try_join_target_ready = \j ->
    case andb
           (andb
             (andb (sched_trace_is_join_target_ready j entry)
               (job_list_contains j known))
             (job_list_contains j ready_targets))
           (negb (job_list_contains j (astas_ready_targets st))) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None
      (astas_dispatched st) (astas_completed st)
      (add_job_once j (astas_ready_targets st)));
     False -> None}}
  in
  let {
   try_complete_job = \j ->
    case andb
           (andb
             (andb (sched_trace_is_complete j entry)
               (job_list_contains j (astas_dispatched st)))
             (negb (job_list_contains j (astas_completed st))))
           (all_dependencies_ready j deps (astas_ready_targets st)) of {
     True -> Some (MkAwkernelSchedTraceAcceptanceState True None
      (astas_dispatched st) (add_job_once j (astas_completed st))
      (astas_ready_targets st));
     False -> None}}
  in
  case sched_trace_is_stutter entry of {
   True -> Some st;
   False ->
    case first_some try_wakeup_job known of {
     Some st' -> Some st';
     None ->
      case first_some try_choose_job known of {
       Some st' -> Some st';
       None ->
        case first_some try_dispatch_job known of {
         Some st' -> Some st';
         None ->
          case first_some try_join_target_ready known of {
           Some st' -> Some st';
           None -> first_some try_complete_job known}}}}}

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

job_in_listb :: JobId -> (List JobId) -> Bool
job_in_listb j xs =
  case xs of {
   Nil -> False;
   Cons x xs' -> orb (eqb0 j x) (job_in_listb j xs')}

job_in_optionb :: (Option JobId) -> JobId -> Bool
job_in_optionb oj j =
  case oj of {
   Some j' -> eqb0 j j';
   None -> False}

row_candidate_visibleb :: AwkernelSchedTraceEntry -> JobId -> Bool
row_candidate_visibleb row j =
  orb
    (orb (job_in_optionb (sched_trace_primary_current row) j)
      (job_in_listb j (aste_runnable row)))
    (job_in_optionb (sched_trace_primary_dispatch_target row) j)

empty_sched_trace_entry :: AwkernelSchedTraceEntry
empty_sched_trace_entry =
  MkAwkernelSchedTraceEntry O EvStutter None Nil False None Nil Nil Nil

fifo_eligible_candidates :: (JobId -> Job) -> Nat -> Schedule -> Time ->
                            (List JobId) -> List JobId
fifo_eligible_candidates jobs m sched t candidates =
  filter (\j -> eligibleb jobs m sched j t) (nodup eq_dec candidates)

choose_top_m_fifo :: (JobId -> Job) -> Nat -> Schedule -> Time -> (List
                     JobId) -> List JobId
choose_top_m_fifo jobs m sched t candidates =
  firstn m (fifo_eligible_candidates jobs m sched t candidates)

global_fifo_top_m_spec :: GenericTopMSchedulingAlgorithm
global_fifo_top_m_spec =
  choose_top_m_fifo

option_job_to_list :: (Option JobId) -> List JobId
option_job_to_list oj =
  case oj of {
   Some j -> Cons j Nil;
   None -> Nil}

append_job_once_preserving :: (List JobId) -> JobId -> List JobId
append_job_once_preserving xs j =
  case job_list_contains j xs of {
   True -> xs;
   False -> app xs (Cons j Nil)}

append_jobs_once_preserving :: (List JobId) -> (List JobId) -> List JobId
append_jobs_once_preserving acc xs =
  case xs of {
   Nil -> acc;
   Cons j xs' ->
    append_jobs_once_preserving (append_job_once_preserving acc j) xs'}

append_option_job_once_preserving :: (List JobId) -> (Option JobId) -> List
                                     JobId
append_option_job_once_preserving acc oj =
  case oj of {
   Some j -> append_job_once_preserving acc j;
   None -> acc}

sched_trace_fifo_candidates :: AwkernelSchedTraceEntry -> List JobId
sched_trace_fifo_candidates entry =
  append_option_job_once_preserving
    (append_jobs_once_preserving
      (option_job_to_list (sched_trace_primary_current entry))
      (aste_runnable entry))
    (sched_trace_primary_dispatch_target entry)

sched_trace_fifo_head :: AwkernelSchedTraceEntry -> Option JobId
sched_trace_fifo_head entry =
  case sched_trace_fifo_candidates entry of {
   Nil -> None;
   Cons j _ -> Some j}

sched_trace_global_fifo_rowb :: AwkernelSchedTraceEntry -> Bool
sched_trace_global_fifo_rowb entry =
  case aste_event entry of {
   EvChoose cpu j ->
    andb (andb (eqb0 (aste_cpu entry) (S O)) (eqb0 cpu (S O)))
      (option_job_eqb (sched_trace_fifo_head entry) (Some j));
   _ -> True}

sched_trace_global_fifo_checkb :: (List AwkernelSchedTraceEntry) -> Bool
sched_trace_global_fifo_checkb sched_trace =
  case sched_trace of {
   Nil -> True;
   Cons entry sched_trace' ->
    andb (sched_trace_global_fifo_rowb entry)
      (sched_trace_global_fifo_checkb sched_trace')}

first_non_fifo_sched_trace_index_from :: Nat -> (List
                                         AwkernelSchedTraceEntry) -> Option
                                         Nat
first_non_fifo_sched_trace_index_from n sched_trace =
  case sched_trace of {
   Nil -> None;
   Cons entry sched_trace' ->
    case sched_trace_global_fifo_rowb entry of {
     True -> first_non_fifo_sched_trace_index_from (S n) sched_trace';
     False -> Some n}}

first_non_fifo_sched_trace_index :: (List AwkernelSchedTraceEntry) -> Option
                                    Nat
first_non_fifo_sched_trace_index sched_trace =
  first_non_fifo_sched_trace_index_from O sched_trace

awk_workload_accepts_global_fifo_sched_trace :: (List AwkernelTaskTraceEntry)
                                                -> (List
                                                AwkernelSchedTraceEntry) ->
                                                Bool
awk_workload_accepts_global_fifo_sched_trace task_trace sched_trace =
  andb (awk_workload_accepts_sched_trace task_trace sched_trace)
    (sched_trace_global_fifo_checkb sched_trace)

job_list_eqb :: (List JobId) -> (List JobId) -> Bool
job_list_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> True;
           Cons _ _ -> False};
   Cons x xs' ->
    case ys of {
     Nil -> False;
     Cons y ys' -> andb (eqb0 x y) (job_list_eqb xs' ys')}}

workload_scheduler_relation_candidates :: AwkernelSchedTraceEntry -> List
                                          JobId
workload_scheduler_relation_candidates entry =
  case aste_event entry of {
   EvChoose cpu _ ->
    case eqb0 cpu (S O) of {
     True -> sched_trace_fifo_candidates entry;
     False -> Nil};
   _ -> Nil}

workload_scheduler_relation_choice :: AwkernelSchedTraceEntry -> List JobId
workload_scheduler_relation_choice entry =
  case aste_event entry of {
   EvChoose cpu j ->
    case eqb0 cpu (S O) of {
     True -> Cons j Nil;
     False -> Nil};
   _ -> Nil}

workload_scheduler_relation_schedule :: (List AwkernelSchedTraceEntry) ->
                                        Schedule
workload_scheduler_relation_schedule sched_trace t c =
  case ltb c (S O) of {
   True ->
    nth_error
      (workload_scheduler_relation_choice
        (nth t sched_trace empty_sched_trace_entry))
      c;
   False -> None}

task_trace_has_completeb :: JobId -> (List AwkernelTaskTraceEntry) -> Bool
task_trace_has_completeb task_id task_trace =
  case task_trace of {
   Nil -> False;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkComplete ->
      orb (eqb0 (atte_subject entry) task_id)
        (task_trace_has_completeb task_id task_trace');
     _ -> task_trace_has_completeb task_id task_trace'}}

count_scheduler_relation_service :: JobId -> (List AwkernelSchedTraceEntry)
                                    -> Nat
count_scheduler_relation_service task_id sched_trace =
  case sched_trace of {
   Nil -> O;
   Cons entry sched_trace' ->
    let {rest = count_scheduler_relation_service task_id sched_trace'} in
    case workload_scheduler_relation_choice entry of {
     Nil -> rest;
     Cons j l ->
      case l of {
       Nil -> case eqb0 j task_id of {
               True -> S rest;
               False -> rest};
       Cons _ _ -> rest}}}

first_scheduler_visible_index_from :: Nat -> Nat -> (List
                                      AwkernelSchedTraceEntry) -> Option 
                                      Nat
first_scheduler_visible_index_from task_id n sched_trace =
  case sched_trace of {
   Nil -> None;
   Cons entry sched_trace' ->
    case row_candidate_visibleb entry task_id of {
     True -> Some n;
     False -> first_scheduler_visible_index_from task_id (S n) sched_trace'}}

first_scheduler_visible_index :: JobId -> (List AwkernelSchedTraceEntry) ->
                                 Option Nat
first_scheduler_visible_index task_id sched_trace =
  first_scheduler_visible_index_from task_id O sched_trace

reconstructed_scheduler_relation_release :: JobId -> (List
                                            AwkernelSchedTraceEntry) -> Nat
reconstructed_scheduler_relation_release task_id sched_trace =
  case first_scheduler_visible_index task_id sched_trace of {
   Some t -> t;
   None -> O}

reconstructed_scheduler_relation_cost :: (List AwkernelTaskTraceEntry) ->
                                         (List AwkernelSchedTraceEntry) ->
                                         JobId -> Nat
reconstructed_scheduler_relation_cost task_trace sched_trace task_id =
  let {service = count_scheduler_relation_service task_id sched_trace} in
  case task_trace_has_completeb task_id task_trace of {
   True -> case service of {
            O -> S O;
            S _ -> service};
   False -> S service}

reconstructed_scheduler_relation_abs_deadline :: (List
                                                 AwkernelTaskTraceEntry) ->
                                                 (List
                                                 AwkernelSchedTraceEntry) ->
                                                 JobId -> Nat
reconstructed_scheduler_relation_abs_deadline task_trace sched_trace task_id =
  add
    (add (reconstructed_scheduler_relation_release task_id sched_trace)
      (reconstructed_scheduler_relation_cost task_trace sched_trace task_id))
    (length sched_trace)

workload_scheduler_relation_jobs :: (List AwkernelTaskTraceEntry) -> (List
                                    AwkernelSchedTraceEntry) -> JobId -> Job
workload_scheduler_relation_jobs task_trace sched_trace task_id =
  MkJob task_id O
    (reconstructed_scheduler_relation_release task_id sched_trace)
    (reconstructed_scheduler_relation_cost task_trace sched_trace task_id)
    (reconstructed_scheduler_relation_abs_deadline task_trace sched_trace
      task_id)
    (\_ -> False)

workload_global_fifo_scheduler_relation_rowb :: (List AwkernelTaskTraceEntry)
                                                -> (List
                                                AwkernelSchedTraceEntry) ->
                                                Time ->
                                                AwkernelSchedTraceEntry ->
                                                Bool
workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry =
  job_list_eqb
    (choose_top_m global_fifo_top_m_spec
      (workload_scheduler_relation_jobs task_trace sched_trace) (S O)
      (workload_scheduler_relation_schedule sched_trace) t
      (workload_scheduler_relation_candidates entry))
    (workload_scheduler_relation_choice entry)

sched_trace_global_fifo_scheduler_relation_check_from :: (List
                                                         AwkernelTaskTraceEntry)
                                                         -> (List
                                                         AwkernelSchedTraceEntry)
                                                         -> Nat -> (List
                                                         AwkernelSchedTraceEntry)
                                                         -> Bool
sched_trace_global_fifo_scheduler_relation_check_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> True;
   Cons entry remaining' ->
    andb
      (workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t
        entry)
      (sched_trace_global_fifo_scheduler_relation_check_from task_trace
        sched_trace (S t) remaining')}

sched_trace_global_fifo_scheduler_relation_checkb :: (List
                                                     AwkernelTaskTraceEntry)
                                                     -> (List
                                                     AwkernelSchedTraceEntry)
                                                     -> Bool
sched_trace_global_fifo_scheduler_relation_checkb task_trace sched_trace =
  sched_trace_global_fifo_scheduler_relation_check_from task_trace
    sched_trace O sched_trace

first_non_scheduler_relation_sched_trace_index_from :: (List
                                                       AwkernelTaskTraceEntry)
                                                       -> (List
                                                       AwkernelSchedTraceEntry)
                                                       -> Nat -> (List
                                                       AwkernelSchedTraceEntry)
                                                       -> Option Nat
first_non_scheduler_relation_sched_trace_index_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> None;
   Cons entry remaining' ->
    case workload_global_fifo_scheduler_relation_rowb task_trace sched_trace
           t entry of {
     True ->
      first_non_scheduler_relation_sched_trace_index_from task_trace
        sched_trace (S t) remaining';
     False -> Some t}}

first_non_scheduler_relation_sched_trace_index :: (List
                                                  AwkernelTaskTraceEntry) ->
                                                  (List
                                                  AwkernelSchedTraceEntry) ->
                                                  Option Nat
first_non_scheduler_relation_sched_trace_index task_trace sched_trace =
  first_non_scheduler_relation_sched_trace_index_from task_trace sched_trace
    O sched_trace

awk_workload_accepts_global_fifo_scheduler_relation_sched_trace :: (List
                                                                   AwkernelTaskTraceEntry)
                                                                   -> (List
                                                                   AwkernelSchedTraceEntry)
                                                                   -> Bool
awk_workload_accepts_global_fifo_scheduler_relation_sched_trace task_trace sched_trace =
  andb (awk_workload_accepts_sched_trace task_trace sched_trace)
    (sched_trace_global_fifo_scheduler_relation_checkb task_trace
      sched_trace)
