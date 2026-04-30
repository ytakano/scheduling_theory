module AwkernelWorkloadAcceptance where

import qualified Prelude

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

length :: (List a1) -> Prelude.Integer
length l =
  case l of {
   Nil -> 0;
   Cons _ l' -> Prelude.succ (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb n m =
  (Prelude.<=) (Prelude.succ n) m

nth :: Prelude.Integer -> (List a1) -> a1 -> a1
nth n l default0 =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            Nil -> default0;
            Cons x _ -> x})
    (\m -> case l of {
            Nil -> default0;
            Cons _ l' -> nth m l' default0})
    n

firstn :: Prelude.Integer -> (List a1) -> List a1
firstn n l =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Nil)
    (\n0 -> case l of {
             Nil -> Nil;
             Cons a l0 -> Cons a (firstn n0 l0)})
    n

in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (List a1) -> Prelude.Bool
in_dec h a l =
  list_rec Prelude.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> iHl}) l

nth_error :: (List a1) -> Prelude.Integer -> Option a1
nth_error l n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> case l of {
            Nil -> None;
            Cons x _ -> Some x})
    (\n0 -> case l of {
             Nil -> None;
             Cons _ l' -> nth_error l' n0})
    n

remove :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (List a1) -> List a1
remove eq_dec x l =
  case l of {
   Nil -> Nil;
   Cons y tl ->
    case eq_dec x y of {
     Prelude.True -> remove eq_dec x tl;
     Prelude.False -> Cons y (remove eq_dec x tl)}}

filter :: (a1 -> Prelude.Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     Prelude.True -> Cons x (filter f l0);
     Prelude.False -> filter f l0}}

nodup :: (a1 -> a1 -> Prelude.Bool) -> (List a1) -> List a1
nodup decA l =
  case l of {
   Nil -> Nil;
   Cons x xs ->
    case in_dec decA x xs of {
     Prelude.True -> nodup decA xs;
     Prelude.False -> Cons x (nodup decA xs)}}

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

of_succ_nat :: Prelude.Integer -> Positive
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> XH)
    (\x -> succ (of_succ_nat x))
    n

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

leb :: Z -> Z -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

of_nat :: Prelude.Integer -> Z
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Z0)
    (\n0 -> Zpos (of_succ_nat n0))
    n

type JobId = Prelude.Integer

type TaskId = Prelude.Integer

type CPU = Prelude.Integer

type Time = Prelude.Integer

data Job =
   MkJob TaskId Prelude.Integer Time Prelude.Integer Time (Time ->
                                                          Prelude.Bool)

job_release :: Job -> Time
job_release j =
  case j of {
   MkJob _ _ job_release0 _ _ _ -> job_release0}

job_cost :: Job -> Prelude.Integer
job_cost j =
  case j of {
   MkJob _ _ _ job_cost0 _ _ -> job_cost0}

job_abs_deadline :: Job -> Time
job_abs_deadline j =
  case j of {
   MkJob _ _ _ _ job_abs_deadline0 _ -> job_abs_deadline0}

job_blocked :: Job -> Time -> Prelude.Bool
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

remove_job :: JobId -> (List JobId) -> List JobId
remove_job j xs =
  case xs of {
   Nil -> Nil;
   Cons x xs' ->
    case (Prelude.==) x j of {
     Prelude.True -> remove_job j xs';
     Prelude.False -> Cons x (remove_job j xs')}}

runs_on :: Schedule -> JobId -> Time -> CPU -> Prelude.Bool
runs_on sched j t c =
  case sched t c of {
   Some j' -> (Prelude.==) j' j;
   None -> Prelude.False}

cpu_count :: Prelude.Integer -> Schedule -> JobId -> Time -> Prelude.Integer
cpu_count m sched j t =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\m' ->
    (Prelude.+)
      (case runs_on sched j t m' of {
        Prelude.True -> Prelude.succ 0;
        Prelude.False -> 0})
      (cpu_count m' sched j t))
    m

service_job :: Prelude.Integer -> Schedule -> JobId -> Time ->
               Prelude.Integer
service_job m sched j t =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\t' -> (Prelude.+) (cpu_count m sched j t') (service_job m sched j t'))
    t

eligibleb :: (JobId -> Job) -> Prelude.Integer -> Schedule -> JobId -> Time
             -> Prelude.Bool
eligibleb jobs m sched j t =
  (Prelude.&&)
    ((Prelude.&&) ((Prelude.<=) (job_release (jobs j)) t)
      (Prelude.not
        ((Prelude.<=) (job_cost (jobs j)) (service_job m sched j t))))
    (Prelude.not (job_blocked (jobs j) t))

type GenericTopMSchedulingAlgorithm =
  (JobId -> Job) -> Prelude.Integer -> Schedule -> Time -> (List JobId) ->
  List JobId
  -- singleton inductive, whose constructor was mkGenericTopMSchedulingAlgorithm

choose_top_m :: GenericTopMSchedulingAlgorithm -> (JobId -> Job) ->
                Prelude.Integer -> Schedule -> Time -> (List JobId) -> List
                JobId
choose_top_m g =
  g

data AwkernelSchedTraceEntry =
   MkAwkernelSchedTraceEntry Prelude.Integer CPU OpEvent (Option JobId)
 (List JobId) Prelude.Bool (Option JobId) (List (Option JobId)) (List
                                                                Prelude.Bool)
 (List (Option JobId))

aste_event_id :: AwkernelSchedTraceEntry -> Prelude.Integer
aste_event_id a =
  case a of {
   MkAwkernelSchedTraceEntry aste_event_id0 _ _ _ _ _ _ _ _ _ ->
    aste_event_id0}

aste_cpu :: AwkernelSchedTraceEntry -> CPU
aste_cpu a =
  case a of {
   MkAwkernelSchedTraceEntry _ aste_cpu0 _ _ _ _ _ _ _ _ -> aste_cpu0}

aste_event :: AwkernelSchedTraceEntry -> OpEvent
aste_event a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ aste_event0 _ _ _ _ _ _ _ -> aste_event0}

aste_current :: AwkernelSchedTraceEntry -> Option JobId
aste_current a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ aste_current0 _ _ _ _ _ _ -> aste_current0}

aste_runnable :: AwkernelSchedTraceEntry -> List JobId
aste_runnable a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ aste_runnable0 _ _ _ _ _ ->
    aste_runnable0}

aste_need_resched :: AwkernelSchedTraceEntry -> Prelude.Bool
aste_need_resched a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ _ aste_need_resched0 _ _ _ _ ->
    aste_need_resched0}

aste_dispatch_target :: AwkernelSchedTraceEntry -> Option JobId
aste_dispatch_target a =
  case a of {
   MkAwkernelSchedTraceEntry _ _ _ _ _ _ aste_dispatch_target0 _ _ _ ->
    aste_dispatch_target0}

sched_trace_primary_current :: AwkernelSchedTraceEntry -> Option JobId
sched_trace_primary_current =
  aste_current

sched_trace_primary_need_resched :: AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_primary_need_resched =
  aste_need_resched

sched_trace_primary_dispatch_target :: AwkernelSchedTraceEntry -> Option
                                       JobId
sched_trace_primary_dispatch_target =
  aste_dispatch_target

data AwkernelTaskTraceKind =
   LkSpawn
 | LkRunnable
 | LkRunnableDeadline
 | LkChoose
 | LkDispatch
 | LkBlock
 | LkUnblock
 | LkJoinWait
 | LkJoinTargetReady
 | LkPeriodicJobComplete
 | LkComplete

data AwkernelWaitClass =
   WcSleep
 | WcIo

data AwkernelUnblockKind =
   UkReady
 | UkTimeout

data AwkernelTaskPolicy =
   AtpGlobalEDF Prelude.Integer
 | AtpPrioritizedFIFO Prelude.Integer
 | AtpPrioritizedRR Prelude.Integer
 | AtpPanicked
 | AtpUnsupported

data AwkernelRunnableDeadlineMetadata =
   MkAwkernelRunnableDeadlineMetadata Prelude.Integer Prelude.Integer
 (Option Prelude.Integer)

ardm_wake_time :: AwkernelRunnableDeadlineMetadata -> Prelude.Integer
ardm_wake_time a =
  case a of {
   MkAwkernelRunnableDeadlineMetadata ardm_wake_time0 _ _ -> ardm_wake_time0}

ardm_absolute_deadline :: AwkernelRunnableDeadlineMetadata -> Prelude.Integer
ardm_absolute_deadline a =
  case a of {
   MkAwkernelRunnableDeadlineMetadata _ ardm_absolute_deadline0 _ ->
    ardm_absolute_deadline0}

ardm_periodic_loop_index :: AwkernelRunnableDeadlineMetadata -> Option
                            Prelude.Integer
ardm_periodic_loop_index a =
  case a of {
   MkAwkernelRunnableDeadlineMetadata _ _ ardm_periodic_loop_index0 ->
    ardm_periodic_loop_index0}

data AwkernelTaskTraceEntry =
   MkAwkernelTaskTraceEntry Prelude.Integer AwkernelTaskTraceKind JobId
 (Option JobId) (Option AwkernelWaitClass) (Option AwkernelUnblockKind)
 (Option AwkernelTaskPolicy) (Option AwkernelRunnableDeadlineMetadata)
 (Option Prelude.Integer)

atte_event_id :: AwkernelTaskTraceEntry -> Prelude.Integer
atte_event_id a =
  case a of {
   MkAwkernelTaskTraceEntry atte_event_id0 _ _ _ _ _ _ _ _ -> atte_event_id0}

atte_kind :: AwkernelTaskTraceEntry -> AwkernelTaskTraceKind
atte_kind a =
  case a of {
   MkAwkernelTaskTraceEntry _ atte_kind0 _ _ _ _ _ _ _ -> atte_kind0}

atte_subject :: AwkernelTaskTraceEntry -> JobId
atte_subject a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ atte_subject0 _ _ _ _ _ _ -> atte_subject0}

atte_related :: AwkernelTaskTraceEntry -> Option JobId
atte_related a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ atte_related0 _ _ _ _ _ -> atte_related0}

atte_wait_class :: AwkernelTaskTraceEntry -> Option AwkernelWaitClass
atte_wait_class a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ _ atte_wait_class0 _ _ _ _ ->
    atte_wait_class0}

atte_unblock_kind :: AwkernelTaskTraceEntry -> Option AwkernelUnblockKind
atte_unblock_kind a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ _ _ atte_unblock_kind0 _ _ _ ->
    atte_unblock_kind0}

atte_policy :: AwkernelTaskTraceEntry -> Option AwkernelTaskPolicy
atte_policy a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ _ _ _ atte_policy0 _ _ -> atte_policy0}

atte_deadline_metadata :: AwkernelTaskTraceEntry -> Option
                          AwkernelRunnableDeadlineMetadata
atte_deadline_metadata a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ _ _ _ _ atte_deadline_metadata0 _ ->
    atte_deadline_metadata0}

atte_periodic_loop_index :: AwkernelTaskTraceEntry -> Option Prelude.Integer
atte_periodic_loop_index a =
  case a of {
   MkAwkernelTaskTraceEntry _ _ _ _ _ _ _ _ atte_periodic_loop_index0 ->
    atte_periodic_loop_index0}

option_job_eqb :: (Option JobId) -> (Option JobId) -> Prelude.Bool
option_job_eqb x y =
  case x of {
   Some j1 ->
    case y of {
     Some j2 -> (Prelude.==) j1 j2;
     None -> Prelude.False};
   None -> case y of {
            Some _ -> Prelude.False;
            None -> Prelude.True}}

job_list_contains :: JobId -> (List JobId) -> Prelude.Bool
job_list_contains j xs =
  case xs of {
   Nil -> Prelude.False;
   Cons x xs' -> (Prelude.||) ((Prelude.==) x j) (job_list_contains j xs')}

insert_job_sorted :: JobId -> (List JobId) -> List JobId
insert_job_sorted j xs =
  case xs of {
   Nil -> Cons j Nil;
   Cons x xs' ->
    case (Prelude.==) j x of {
     Prelude.True -> Cons x xs';
     Prelude.False ->
      case (Prelude.<=) j x of {
       Prelude.True -> Cons j (Cons x xs');
       Prelude.False -> Cons x (insert_job_sorted j xs')}}}

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

pair_list_contains :: (Prod JobId JobId) -> (List (Prod JobId JobId)) ->
                      Prelude.Bool
pair_list_contains x xs =
  case xs of {
   Nil -> Prelude.False;
   Cons p xs' ->
    case p of {
     Pair a b ->
      case x of {
       Pair x1 x2 ->
        (Prelude.||) ((Prelude.&&) ((Prelude.==) a x1) ((Prelude.==) b x2))
          (pair_list_contains x xs')}}}

add_pair_once :: (Prod JobId JobId) -> (List (Prod JobId JobId)) -> List
                 (Prod JobId JobId)
add_pair_once x xs =
  case pair_list_contains x xs of {
   Prelude.True -> xs;
   Prelude.False -> Cons x xs}

all_dependencies_ready :: JobId -> (List (Prod JobId JobId)) -> (List
                          JobId) -> Prelude.Bool
all_dependencies_ready task_id deps ready_targets =
  case deps of {
   Nil -> Prelude.True;
   Cons p deps' ->
    case p of {
     Pair waiter target ->
      case (Prelude.==) waiter task_id of {
       Prelude.True ->
        (Prelude.&&) (job_list_contains target ready_targets)
          (all_dependencies_ready task_id deps' ready_targets);
       Prelude.False -> all_dependencies_ready task_id deps' ready_targets}}}

bool_of_option_none :: (Option a1) -> Prelude.Bool
bool_of_option_none oj =
  case oj of {
   Some _ -> Prelude.False;
   None -> Prelude.True}

bool_of_wait_class_some :: (Option AwkernelWaitClass) -> Prelude.Bool
bool_of_wait_class_some owc =
  case owc of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

bool_of_unblock_kind_some :: (Option AwkernelUnblockKind) -> Prelude.Bool
bool_of_unblock_kind_some ouk =
  case ouk of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

bool_of_task_policy_none :: (Option AwkernelTaskPolicy) -> Prelude.Bool
bool_of_task_policy_none op =
  case op of {
   Some _ -> Prelude.False;
   None -> Prelude.True}

bool_of_task_policy_some :: (Option AwkernelTaskPolicy) -> Prelude.Bool
bool_of_task_policy_some op =
  case op of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

task_policy_global_fifo_supportedb :: AwkernelTaskPolicy -> Prelude.Bool
task_policy_global_fifo_supportedb policy =
  case policy of {
   AtpPrioritizedFIFO _ -> Prelude.True;
   _ -> Prelude.False}

task_policy_global_edf_supportedb :: AwkernelTaskPolicy -> Prelude.Bool
task_policy_global_edf_supportedb policy =
  case policy of {
   AtpGlobalEDF _ -> Prelude.True;
   _ -> Prelude.False}

task_policy_edf_fifo_supportedb :: AwkernelTaskPolicy -> Prelude.Bool
task_policy_edf_fifo_supportedb policy =
  (Prelude.||) (task_policy_global_edf_supportedb policy)
    (task_policy_global_fifo_supportedb policy)

option_task_policy_global_fifo_supportedb :: (Option AwkernelTaskPolicy) ->
                                             Prelude.Bool
option_task_policy_global_fifo_supportedb policy =
  case policy of {
   Some policy' -> task_policy_global_fifo_supportedb policy';
   None -> Prelude.False}

option_task_policy_global_edf_supportedb :: (Option AwkernelTaskPolicy) ->
                                            Prelude.Bool
option_task_policy_global_edf_supportedb policy =
  case policy of {
   Some policy' -> task_policy_global_edf_supportedb policy';
   None -> Prelude.False}

option_task_policy_edf_fifo_supportedb :: (Option AwkernelTaskPolicy) ->
                                          Prelude.Bool
option_task_policy_edf_fifo_supportedb policy =
  case policy of {
   Some policy' -> task_policy_edf_fifo_supportedb policy';
   None -> Prelude.False}

wait_class_eqb :: AwkernelWaitClass -> AwkernelWaitClass -> Prelude.Bool
wait_class_eqb lhs rhs =
  case lhs of {
   WcSleep -> case rhs of {
               WcSleep -> Prelude.True;
               WcIo -> Prelude.False};
   WcIo -> case rhs of {
            WcSleep -> Prelude.False;
            WcIo -> Prelude.True}}

task_trace_metadata_empty :: AwkernelTaskTraceEntry -> Prelude.Bool
task_trace_metadata_empty entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) (bool_of_option_none (atte_related entry))
            (bool_of_option_none (atte_wait_class entry)))
          (bool_of_option_none (atte_unblock_kind entry)))
        (bool_of_task_policy_none (atte_policy entry)))
      (bool_of_option_none (atte_deadline_metadata entry)))
    (bool_of_option_none (atte_periodic_loop_index entry))

task_trace_has_wait_class_only :: AwkernelTaskTraceEntry -> Prelude.Bool
task_trace_has_wait_class_only entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) (bool_of_option_none (atte_related entry))
            (bool_of_wait_class_some (atte_wait_class entry)))
          (bool_of_option_none (atte_unblock_kind entry)))
        (bool_of_task_policy_none (atte_policy entry)))
      (bool_of_option_none (atte_deadline_metadata entry)))
    (bool_of_option_none (atte_periodic_loop_index entry))

task_trace_has_wait_and_unblock_kind :: AwkernelTaskTraceEntry ->
                                        Prelude.Bool
task_trace_has_wait_and_unblock_kind entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) (bool_of_option_none (atte_related entry))
            (bool_of_wait_class_some (atte_wait_class entry)))
          (bool_of_unblock_kind_some (atte_unblock_kind entry)))
        (bool_of_task_policy_none (atte_policy entry)))
      (bool_of_option_none (atte_deadline_metadata entry)))
    (bool_of_option_none (atte_periodic_loop_index entry))

blocked_task_class :: JobId -> (List (Prod JobId AwkernelWaitClass)) ->
                      Option AwkernelWaitClass
blocked_task_class task_id blocked =
  case blocked of {
   Nil -> None;
   Cons p blocked' ->
    case p of {
     Pair blocked_task wait_class ->
      case (Prelude.==) blocked_task task_id of {
       Prelude.True -> Some wait_class;
       Prelude.False -> blocked_task_class task_id blocked'}}}

blocked_task_contains :: JobId -> (List (Prod JobId AwkernelWaitClass)) ->
                         Prelude.Bool
blocked_task_contains task_id blocked =
  case blocked_task_class task_id blocked of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

remove_blocked_task :: JobId -> (List (Prod JobId AwkernelWaitClass)) -> List
                       (Prod JobId AwkernelWaitClass)
remove_blocked_task task_id blocked =
  case blocked of {
   Nil -> Nil;
   Cons p blocked' ->
    case p of {
     Pair blocked_task wait_class ->
      case (Prelude.==) blocked_task task_id of {
       Prelude.True -> remove_blocked_task task_id blocked';
       Prelude.False -> Cons (Pair blocked_task wait_class)
        (remove_blocked_task task_id blocked')}}}

periodic_job_complete_contains :: JobId -> Prelude.Integer -> (List
                                  (Prod JobId Prelude.Integer)) ->
                                  Prelude.Bool
periodic_job_complete_contains task_id loop_index completions =
  case completions of {
   Nil -> Prelude.False;
   Cons p completions' ->
    case p of {
     Pair completed_task completed_loop ->
      (Prelude.||)
        ((Prelude.&&) ((Prelude.==) completed_task task_id)
          ((Prelude.==) completed_loop loop_index))
        (periodic_job_complete_contains task_id loop_index completions')}}

add_periodic_job_complete_once :: JobId -> Prelude.Integer -> (List
                                  (Prod JobId Prelude.Integer)) -> List
                                  (Prod JobId Prelude.Integer)
add_periodic_job_complete_once task_id loop_index completions =
  case periodic_job_complete_contains task_id loop_index completions of {
   Prelude.True -> completions;
   Prelude.False -> Cons (Pair task_id loop_index) completions}

sched_trace_event_is_wakeup :: JobId -> AwkernelSchedTraceEntry ->
                               Prelude.Bool
sched_trace_event_is_wakeup j entry =
  case aste_event entry of {
   EvWakeup j' -> (Prelude.==) j' j;
   _ -> Prelude.False}

sched_trace_event_is_block :: JobId -> AwkernelSchedTraceEntry ->
                              Prelude.Bool
sched_trace_event_is_block j entry =
  case aste_event entry of {
   EvBlock j' -> (Prelude.==) j' j;
   _ -> Prelude.False}

sched_trace_event_is_choose :: JobId -> JobId -> AwkernelSchedTraceEntry ->
                               Prelude.Bool
sched_trace_event_is_choose cpu j entry =
  case aste_event entry of {
   EvChoose c' j' -> (Prelude.&&) ((Prelude.==) c' cpu) ((Prelude.==) j' j);
   _ -> Prelude.False}

sched_trace_event_is_dispatch :: JobId -> JobId -> AwkernelSchedTraceEntry ->
                                 Prelude.Bool
sched_trace_event_is_dispatch cpu j entry =
  case aste_event entry of {
   EvDispatch c' j' -> (Prelude.&&) ((Prelude.==) c' cpu) ((Prelude.==) j' j);
   _ -> Prelude.False}

sched_trace_event_is_complete :: JobId -> AwkernelSchedTraceEntry ->
                                 Prelude.Bool
sched_trace_event_is_complete j entry =
  case aste_event entry of {
   EvComplete j' -> (Prelude.==) j' j;
   _ -> Prelude.False}

sched_trace_event_is_join_target_ready :: JobId -> AwkernelSchedTraceEntry ->
                                          Prelude.Bool
sched_trace_event_is_join_target_ready j entry =
  case aste_event entry of {
   EvJoinTargetReady j' -> (Prelude.==) j' j;
   _ -> Prelude.False}

sched_trace_event_is_stutter :: AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_event_is_stutter entry =
  case aste_event entry of {
   EvStutter -> Prelude.True;
   _ -> Prelude.False}

sched_trace_is_wakeup :: JobId -> AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_wakeup j entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) ((Prelude.==) (aste_cpu entry) 0)
            (sched_trace_event_is_wakeup j entry))
          (bool_of_option_none (sched_trace_primary_current entry)))
        (job_list_contains j (aste_runnable entry)))
      (eqb (sched_trace_primary_need_resched entry) Prelude.False))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_block :: JobId -> AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_block j entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
          (sched_trace_event_is_block j entry))
        (bool_of_option_none (sched_trace_primary_current entry)))
      (eqb (sched_trace_primary_need_resched entry) Prelude.True))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_choose :: JobId -> AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_choose j entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
          (sched_trace_event_is_choose (Prelude.succ 0) j entry))
        (bool_of_option_none (sched_trace_primary_current entry)))
      (job_list_contains j (aste_runnable entry)))
    (option_job_eqb (sched_trace_primary_dispatch_target entry) (Some j))

sched_trace_is_dispatch :: JobId -> AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_dispatch j entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
          (sched_trace_event_is_dispatch (Prelude.succ 0) j entry))
        (option_job_eqb (sched_trace_primary_current entry) (Some j)))
      (eqb (sched_trace_primary_need_resched entry) Prelude.False))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_complete :: JobId -> AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_complete j entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
          (sched_trace_event_is_complete j entry))
        (bool_of_option_none (sched_trace_primary_current entry)))
      (eqb (sched_trace_primary_need_resched entry) Prelude.True))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

sched_trace_is_join_target_ready :: JobId -> AwkernelSchedTraceEntry ->
                                    Prelude.Bool
sched_trace_is_join_target_ready j entry =
  (Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
    (sched_trace_event_is_join_target_ready j entry)

sched_trace_is_stutter :: AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_is_stutter entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
        (sched_trace_event_is_stutter entry))
      (bool_of_option_none (sched_trace_primary_current entry)))
    (bool_of_option_none (sched_trace_primary_dispatch_target entry))

data AwkernelTaskTraceSummary =
   MkAwkernelTaskTraceSummary (Option JobId) (List JobId) (List
                                                          (Prod JobId
                                                          AwkernelTaskPolicy))
 (List (Prod Prelude.Integer (Prod JobId Prelude.Integer))) (List
                                                            (Prod JobId
                                                            JobId)) (List
                                                                    JobId)
 (List (Prod JobId AwkernelWaitClass)) (List
                                       (Prod Prelude.Integer
                                       (Prod JobId Prelude.Bool))) (List
                                                                   (Prod
                                                                   JobId
                                                                   Prelude.Integer))

atts_root_task :: AwkernelTaskTraceSummary -> Option JobId
atts_root_task a =
  case a of {
   MkAwkernelTaskTraceSummary atts_root_task0 _ _ _ _ _ _ _ _ ->
    atts_root_task0}

atts_known_tasks :: AwkernelTaskTraceSummary -> List JobId
atts_known_tasks a =
  case a of {
   MkAwkernelTaskTraceSummary _ atts_known_tasks0 _ _ _ _ _ _ _ ->
    atts_known_tasks0}

atts_task_policies :: AwkernelTaskTraceSummary -> List
                      (Prod JobId AwkernelTaskPolicy)
atts_task_policies a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ atts_task_policies0 _ _ _ _ _ _ ->
    atts_task_policies0}

atts_edf_deadlines :: AwkernelTaskTraceSummary -> List
                      (Prod Prelude.Integer (Prod JobId Prelude.Integer))
atts_edf_deadlines a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ atts_edf_deadlines0 _ _ _ _ _ ->
    atts_edf_deadlines0}

atts_completion_deps :: AwkernelTaskTraceSummary -> List (Prod JobId JobId)
atts_completion_deps a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ _ atts_completion_deps0 _ _ _ _ ->
    atts_completion_deps0}

atts_ready_targets :: AwkernelTaskTraceSummary -> List JobId
atts_ready_targets a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ _ _ atts_ready_targets0 _ _ _ ->
    atts_ready_targets0}

atts_blocked_tasks :: AwkernelTaskTraceSummary -> List
                      (Prod JobId AwkernelWaitClass)
atts_blocked_tasks a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ _ _ _ atts_blocked_tasks0 _ _ ->
    atts_blocked_tasks0}

atts_block_transitions :: AwkernelTaskTraceSummary -> List
                          (Prod Prelude.Integer (Prod JobId Prelude.Bool))
atts_block_transitions a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ _ _ _ _ atts_block_transitions0 _ ->
    atts_block_transitions0}

atts_periodic_job_completions :: AwkernelTaskTraceSummary -> List
                                 (Prod JobId Prelude.Integer)
atts_periodic_job_completions a =
  case a of {
   MkAwkernelTaskTraceSummary _ _ _ _ _ _ _ _
    atts_periodic_job_completions0 -> atts_periodic_job_completions0}

initial_task_trace_summary :: AwkernelTaskTraceSummary
initial_task_trace_summary =
  MkAwkernelTaskTraceSummary None Nil Nil Nil Nil Nil Nil Nil Nil

add_task_policy :: JobId -> AwkernelTaskPolicy -> (List
                   (Prod JobId AwkernelTaskPolicy)) -> List
                   (Prod JobId AwkernelTaskPolicy)
add_task_policy task_id policy policies =
  Cons (Pair task_id policy) policies

task_policy_table_all_global_fifo :: (List (Prod JobId AwkernelTaskPolicy))
                                     -> Prelude.Bool
task_policy_table_all_global_fifo policies =
  case policies of {
   Nil -> Prelude.True;
   Cons p policies' ->
    case p of {
     Pair _ policy ->
      (Prelude.&&) (task_policy_global_fifo_supportedb policy)
        (task_policy_table_all_global_fifo policies')}}

task_policy_table_all_global_edf :: (List (Prod JobId AwkernelTaskPolicy)) ->
                                    Prelude.Bool
task_policy_table_all_global_edf policies =
  case policies of {
   Nil -> Prelude.True;
   Cons p policies' ->
    case p of {
     Pair _ policy ->
      (Prelude.&&) (task_policy_global_edf_supportedb policy)
        (task_policy_table_all_global_edf policies')}}

task_policy_table_all_edf_fifo :: (List (Prod JobId AwkernelTaskPolicy)) ->
                                  Prelude.Bool
task_policy_table_all_edf_fifo policies =
  case policies of {
   Nil -> Prelude.True;
   Cons p policies' ->
    case p of {
     Pair _ policy ->
      (Prelude.&&) (task_policy_edf_fifo_supportedb policy)
        (task_policy_table_all_edf_fifo policies')}}

add_edf_deadline_evidence :: Prelude.Integer -> JobId -> Prelude.Integer ->
                             (List
                             (Prod Prelude.Integer
                             (Prod JobId Prelude.Integer))) -> List
                             (Prod Prelude.Integer
                             (Prod JobId Prelude.Integer))
add_edf_deadline_evidence event_id task_id absolute_deadline deadlines =
  app deadlines (Cons (Pair event_id (Pair task_id absolute_deadline)) Nil)

task_trace_edf_deadline_at_from :: Prelude.Integer -> JobId -> (List
                                   (Prod Prelude.Integer
                                   (Prod JobId Prelude.Integer))) -> (Option
                                   Prelude.Integer) -> Option Prelude.Integer
task_trace_edf_deadline_at_from event_id task_id deadlines deadline =
  case deadlines of {
   Nil -> deadline;
   Cons p deadlines' ->
    case p of {
     Pair deadline_event_id p0 ->
      case p0 of {
       Pair deadline_task absolute_deadline ->
        let {
         deadline' = case ltb deadline_event_id event_id of {
                      Prelude.True ->
                       case (Prelude.==) deadline_task task_id of {
                        Prelude.True -> Some absolute_deadline;
                        Prelude.False -> deadline};
                      Prelude.False -> deadline}}
        in
        task_trace_edf_deadline_at_from event_id task_id deadlines' deadline'}}}

task_trace_edf_deadline_at :: AwkernelTaskTraceSummary -> Prelude.Integer ->
                              JobId -> Option Prelude.Integer
task_trace_edf_deadline_at summary event_id task_id =
  task_trace_edf_deadline_at_from event_id task_id
    (atts_edf_deadlines summary) None

add_block_transition :: Prelude.Integer -> JobId -> Prelude.Bool -> (List
                        (Prod Prelude.Integer (Prod JobId Prelude.Bool))) ->
                        List (Prod Prelude.Integer (Prod JobId Prelude.Bool))
add_block_transition event_id task_id is_block transitions =
  app transitions (Cons (Pair event_id (Pair task_id is_block)) Nil)

task_trace_blocked_at_from :: Prelude.Integer -> JobId -> (List
                              (Prod Prelude.Integer
                              (Prod JobId Prelude.Bool))) -> Prelude.Bool ->
                              Prelude.Bool
task_trace_blocked_at_from event_id task_id transitions blocked =
  case transitions of {
   Nil -> blocked;
   Cons p transitions' ->
    case p of {
     Pair transition_event_id p0 ->
      case p0 of {
       Pair transition_task is_block ->
        let {
         blocked' = case ltb transition_event_id event_id of {
                     Prelude.True ->
                      case (Prelude.==) transition_task task_id of {
                       Prelude.True -> is_block;
                       Prelude.False -> blocked};
                     Prelude.False -> blocked}}
        in
        task_trace_blocked_at_from event_id task_id transitions' blocked'}}}

task_trace_blocked_at :: AwkernelTaskTraceSummary -> Prelude.Integer -> JobId
                         -> Prelude.Bool
task_trace_blocked_at summary event_id task_id =
  task_trace_blocked_at_from event_id task_id
    (atts_block_transitions summary) Prelude.False

task_trace_runnable_deadline_row_valid :: AwkernelTaskTraceSummary ->
                                          AwkernelTaskTraceEntry ->
                                          Prelude.Bool
task_trace_runnable_deadline_row_valid summary entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          (job_list_contains (atte_subject entry) (atts_known_tasks summary))
          (bool_of_option_none (atte_related entry)))
        (bool_of_option_none (atte_wait_class entry)))
      (bool_of_option_none (atte_unblock_kind entry)))
    (case atte_policy entry of {
      Some a ->
       case a of {
        AtpGlobalEDF relative_deadline ->
         case atte_deadline_metadata entry of {
          Some deadline_metadata ->
           (Prelude.&&)
             ((Prelude.==) (ardm_absolute_deadline deadline_metadata)
               ((Prelude.+) (ardm_wake_time deadline_metadata)
                 relative_deadline))
             (case ardm_periodic_loop_index deadline_metadata of {
               Some metadata_loop_index ->
                case atte_periodic_loop_index entry of {
                 Some entry_loop_index ->
                  (Prelude.==) metadata_loop_index entry_loop_index;
                 None -> Prelude.False};
               None ->
                case atte_periodic_loop_index entry of {
                 Some _ -> Prelude.False;
                 None -> Prelude.True}});
          None -> Prelude.False};
        _ -> Prelude.False};
      None -> Prelude.False})

task_trace_periodic_job_complete_row_valid :: AwkernelTaskTraceSummary ->
                                              AwkernelTaskTraceEntry ->
                                              Prelude.Bool
task_trace_periodic_job_complete_row_valid summary entry =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&)
            ((Prelude.&&)
              (job_list_contains (atte_subject entry)
                (atts_known_tasks summary))
              (bool_of_option_none (atte_related entry)))
            (bool_of_option_none (atte_wait_class entry)))
          (bool_of_option_none (atte_unblock_kind entry)))
        (bool_of_task_policy_none (atte_policy entry)))
      (bool_of_option_none (atte_deadline_metadata entry)))
    (case atte_periodic_loop_index entry of {
      Some loop_index ->
       Prelude.not
         (periodic_job_complete_contains (atte_subject entry) loop_index
           (atts_periodic_job_completions summary));
      None -> Prelude.False})

task_trace_entry_valid :: AwkernelTaskTraceSummary -> AwkernelTaskTraceEntry
                          -> Prelude.Bool
task_trace_entry_valid summary entry =
  case atte_kind entry of {
   LkSpawn ->
    (Prelude.&&)
      (Prelude.not
        (job_list_contains (atte_subject entry) (atts_known_tasks summary)))
      (case atte_related entry of {
        Some parent ->
         (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&)
               ((Prelude.&&)
                 ((Prelude.&&)
                   (job_list_contains parent (atts_known_tasks summary))
                   (bool_of_option_none (atte_wait_class entry)))
                 (bool_of_option_none (atte_unblock_kind entry)))
               (bool_of_task_policy_some (atte_policy entry)))
             (bool_of_option_none (atte_deadline_metadata entry)))
           (bool_of_option_none (atte_periodic_loop_index entry));
        None ->
         (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&)
               ((Prelude.&&)
                 ((Prelude.&&) (option_job_eqb (atts_root_task summary) None)
                   (bool_of_option_none (atte_wait_class entry)))
                 (bool_of_option_none (atte_unblock_kind entry)))
               (bool_of_task_policy_some (atte_policy entry)))
             (bool_of_option_none (atte_deadline_metadata entry)))
           (bool_of_option_none (atte_periodic_loop_index entry))});
   LkRunnableDeadline -> task_trace_runnable_deadline_row_valid summary entry;
   LkBlock ->
    (Prelude.&&)
      ((Prelude.&&)
        (job_list_contains (atte_subject entry) (atts_known_tasks summary))
        (Prelude.not
          (blocked_task_contains (atte_subject entry)
            (atts_blocked_tasks summary))))
      (task_trace_has_wait_class_only entry);
   LkUnblock ->
    (Prelude.&&)
      ((Prelude.&&)
        (job_list_contains (atte_subject entry) (atts_known_tasks summary))
        (task_trace_has_wait_and_unblock_kind entry))
      (case atte_wait_class entry of {
        Some wait_class ->
         case blocked_task_class (atte_subject entry)
                (atts_blocked_tasks summary) of {
          Some blocked_wait_class ->
           wait_class_eqb wait_class blocked_wait_class;
          None -> Prelude.False};
        None -> Prelude.False});
   LkJoinWait ->
    case atte_related entry of {
     Some target ->
      (Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&)
            ((Prelude.&&)
              ((Prelude.&&)
                (job_list_contains (atte_subject entry)
                  (atts_known_tasks summary))
                (job_list_contains target (atts_known_tasks summary)))
              (bool_of_option_none (atte_wait_class entry)))
            (bool_of_option_none (atte_unblock_kind entry)))
          (bool_of_option_none (atte_deadline_metadata entry)))
        (bool_of_option_none (atte_periodic_loop_index entry));
     None -> Prelude.False};
   LkJoinTargetReady ->
    case atte_related entry of {
     Some _ -> Prelude.False;
     None ->
      (Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&)
            ((Prelude.&&)
              ((Prelude.&&)
                (job_list_contains (atte_subject entry)
                  (atts_known_tasks summary))
                (Prelude.not
                  (job_list_contains (atte_subject entry)
                    (atts_ready_targets summary))))
              (bool_of_option_none (atte_wait_class entry)))
            (bool_of_option_none (atte_unblock_kind entry)))
          (bool_of_option_none (atte_deadline_metadata entry)))
        (bool_of_option_none (atte_periodic_loop_index entry))};
   LkPeriodicJobComplete ->
    task_trace_periodic_job_complete_row_valid summary entry;
   _ ->
    (Prelude.&&)
      (job_list_contains (atte_subject entry) (atts_known_tasks summary))
      (task_trace_metadata_empty entry)}

task_trace_entry_step :: AwkernelTaskTraceSummary -> AwkernelTaskTraceEntry
                         -> AwkernelTaskTraceSummary
task_trace_entry_step summary entry =
  case atte_kind entry of {
   LkSpawn -> MkAwkernelTaskTraceSummary
    (case atte_related entry of {
      Some _ -> atts_root_task summary;
      None -> Some (atte_subject entry)})
    (add_job_once (atte_subject entry) (atts_known_tasks summary))
    (case atte_policy entry of {
      Some policy ->
       add_task_policy (atte_subject entry) policy
         (atts_task_policies summary);
      None -> atts_task_policies summary})
    (atts_edf_deadlines summary) (atts_completion_deps summary)
    (atts_ready_targets summary) (atts_blocked_tasks summary)
    (atts_block_transitions summary) (atts_periodic_job_completions summary);
   LkRunnableDeadline -> MkAwkernelTaskTraceSummary (atts_root_task summary)
    (atts_known_tasks summary) (atts_task_policies summary)
    (case atte_deadline_metadata entry of {
      Some deadline_metadata ->
       add_edf_deadline_evidence (atte_event_id entry) (atte_subject entry)
         (ardm_absolute_deadline deadline_metadata)
         (atts_edf_deadlines summary);
      None -> atts_edf_deadlines summary})
    (atts_completion_deps summary) (atts_ready_targets summary)
    (atts_blocked_tasks summary) (atts_block_transitions summary)
    (atts_periodic_job_completions summary);
   LkBlock -> MkAwkernelTaskTraceSummary (atts_root_task summary)
    (atts_known_tasks summary) (atts_task_policies summary)
    (atts_edf_deadlines summary) (atts_completion_deps summary)
    (atts_ready_targets summary) (Cons (Pair (atte_subject entry)
    (case atte_wait_class entry of {
      Some wait_class -> wait_class;
      None -> WcSleep}))
    (atts_blocked_tasks summary))
    (add_block_transition (atte_event_id entry) (atte_subject entry)
      Prelude.True (atts_block_transitions summary))
    (atts_periodic_job_completions summary);
   LkUnblock -> MkAwkernelTaskTraceSummary (atts_root_task summary)
    (atts_known_tasks summary) (atts_task_policies summary)
    (atts_edf_deadlines summary) (atts_completion_deps summary)
    (atts_ready_targets summary)
    (remove_blocked_task (atte_subject entry) (atts_blocked_tasks summary))
    (add_block_transition (atte_event_id entry) (atte_subject entry)
      Prelude.False (atts_block_transitions summary))
    (atts_periodic_job_completions summary);
   LkJoinWait ->
    case atte_related entry of {
     Some target -> MkAwkernelTaskTraceSummary (atts_root_task summary)
      (atts_known_tasks summary) (atts_task_policies summary)
      (atts_edf_deadlines summary)
      (add_pair_once (Pair (atte_subject entry) target)
        (atts_completion_deps summary))
      (atts_ready_targets summary) (atts_blocked_tasks summary)
      (atts_block_transitions summary)
      (atts_periodic_job_completions summary);
     None -> summary};
   LkJoinTargetReady -> MkAwkernelTaskTraceSummary (atts_root_task summary)
    (atts_known_tasks summary) (atts_task_policies summary)
    (atts_edf_deadlines summary) (atts_completion_deps summary)
    (add_job_once (atte_subject entry) (atts_ready_targets summary))
    (atts_blocked_tasks summary) (atts_block_transitions summary)
    (atts_periodic_job_completions summary);
   LkPeriodicJobComplete -> MkAwkernelTaskTraceSummary
    (atts_root_task summary) (atts_known_tasks summary)
    (atts_task_policies summary) (atts_edf_deadlines summary)
    (atts_completion_deps summary) (atts_ready_targets summary)
    (atts_blocked_tasks summary) (atts_block_transitions summary)
    (case atte_periodic_loop_index entry of {
      Some loop_index ->
       add_periodic_job_complete_once (atte_subject entry) loop_index
         (atts_periodic_job_completions summary);
      None -> atts_periodic_job_completions summary});
   _ -> summary}

summarize_task_trace :: AwkernelTaskTraceSummary -> (List
                        AwkernelTaskTraceEntry) -> Option
                        AwkernelTaskTraceSummary
summarize_task_trace summary task_trace =
  case task_trace of {
   Nil -> Some summary;
   Cons entry task_trace' ->
    case task_trace_entry_valid summary entry of {
     Prelude.True ->
      summarize_task_trace (task_trace_entry_step summary entry) task_trace';
     Prelude.False -> None}}

task_trace_all_global_fifo_policyb :: (List AwkernelTaskTraceEntry) ->
                                      Prelude.Bool
task_trace_all_global_fifo_policyb task_trace =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary ->
    task_policy_table_all_global_fifo (atts_task_policies summary);
   None -> Prelude.False}

task_trace_all_global_edf_policyb :: (List AwkernelTaskTraceEntry) ->
                                     Prelude.Bool
task_trace_all_global_edf_policyb task_trace =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary ->
    task_policy_table_all_global_edf (atts_task_policies summary);
   None -> Prelude.False}

task_trace_all_edf_fifo_policyb :: (List AwkernelTaskTraceEntry) ->
                                   Prelude.Bool
task_trace_all_edf_fifo_policyb task_trace =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary ->
    task_policy_table_all_edf_fifo (atts_task_policies summary);
   None -> Prelude.False}

first_non_global_fifo_task_policy_index_from :: Prelude.Integer -> (List
                                                AwkernelTaskTraceEntry) ->
                                                Option Prelude.Integer
first_non_global_fifo_task_policy_index_from n task_trace =
  case task_trace of {
   Nil -> None;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkSpawn ->
      case option_task_policy_global_fifo_supportedb (atte_policy entry) of {
       Prelude.True ->
        first_non_global_fifo_task_policy_index_from (Prelude.succ n)
          task_trace';
       Prelude.False -> Some n};
     _ ->
      first_non_global_fifo_task_policy_index_from (Prelude.succ n)
        task_trace'}}

first_non_global_fifo_task_policy_index :: (List AwkernelTaskTraceEntry) ->
                                           Option Prelude.Integer
first_non_global_fifo_task_policy_index task_trace =
  first_non_global_fifo_task_policy_index_from 0 task_trace

first_non_global_edf_task_policy_index_from :: Prelude.Integer -> (List
                                               AwkernelTaskTraceEntry) ->
                                               Option Prelude.Integer
first_non_global_edf_task_policy_index_from n task_trace =
  case task_trace of {
   Nil -> None;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkSpawn ->
      case option_task_policy_global_edf_supportedb (atte_policy entry) of {
       Prelude.True ->
        first_non_global_edf_task_policy_index_from (Prelude.succ n)
          task_trace';
       Prelude.False -> Some n};
     _ ->
      first_non_global_edf_task_policy_index_from (Prelude.succ n)
        task_trace'}}

first_non_global_edf_task_policy_index :: (List AwkernelTaskTraceEntry) ->
                                          Option Prelude.Integer
first_non_global_edf_task_policy_index task_trace =
  first_non_global_edf_task_policy_index_from 0 task_trace

first_non_edf_fifo_task_policy_index_from :: Prelude.Integer -> (List
                                             AwkernelTaskTraceEntry) ->
                                             Option Prelude.Integer
first_non_edf_fifo_task_policy_index_from n task_trace =
  case task_trace of {
   Nil -> None;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkSpawn ->
      case option_task_policy_edf_fifo_supportedb (atte_policy entry) of {
       Prelude.True ->
        first_non_edf_fifo_task_policy_index_from (Prelude.succ n)
          task_trace';
       Prelude.False -> Some n};
     _ ->
      first_non_edf_fifo_task_policy_index_from (Prelude.succ n) task_trace'}}

first_non_edf_fifo_task_policy_index :: (List AwkernelTaskTraceEntry) ->
                                        Option Prelude.Integer
first_non_edf_fifo_task_policy_index task_trace =
  first_non_edf_fifo_task_policy_index_from 0 task_trace

first_invalid_runnable_deadline_task_trace_index_from :: AwkernelTaskTraceSummary
                                                         -> Prelude.Integer
                                                         -> (List
                                                         AwkernelTaskTraceEntry)
                                                         -> Option
                                                         Prelude.Integer
first_invalid_runnable_deadline_task_trace_index_from summary n task_trace =
  case task_trace of {
   Nil -> None;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkRunnableDeadline ->
      case task_trace_runnable_deadline_row_valid summary entry of {
       Prelude.True ->
        first_invalid_runnable_deadline_task_trace_index_from
          (task_trace_entry_step summary entry) (Prelude.succ n) task_trace';
       Prelude.False -> Some n};
     _ ->
      let {
       summary' = case task_trace_entry_valid summary entry of {
                   Prelude.True -> task_trace_entry_step summary entry;
                   Prelude.False -> summary}}
      in
      first_invalid_runnable_deadline_task_trace_index_from summary'
        (Prelude.succ n) task_trace'}}

first_invalid_runnable_deadline_task_trace_index :: (List
                                                    AwkernelTaskTraceEntry)
                                                    -> Option Prelude.Integer
first_invalid_runnable_deadline_task_trace_index task_trace =
  first_invalid_runnable_deadline_task_trace_index_from
    initial_task_trace_summary 0 task_trace

data AwkernelSchedTraceAcceptanceState =
   MkAwkernelSchedTraceAcceptanceState Prelude.Bool (Option JobId) (List
                                                                   JobId)
 (List JobId) (List JobId) (List JobId)

astas_started :: AwkernelSchedTraceAcceptanceState -> Prelude.Bool
astas_started a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState astas_started0 _ _ _ _ _ ->
    astas_started0}

astas_selected :: AwkernelSchedTraceAcceptanceState -> Option JobId
astas_selected a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ astas_selected0 _ _ _ _ ->
    astas_selected0}

astas_dispatched :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_dispatched a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ astas_dispatched0 _ _ _ ->
    astas_dispatched0}

astas_completed :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_completed a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ astas_completed0 _ _ ->
    astas_completed0}

astas_ready_targets :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_ready_targets a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ _ astas_ready_targets0 _ ->
    astas_ready_targets0}

astas_blocked :: AwkernelSchedTraceAcceptanceState -> List JobId
astas_blocked a =
  case a of {
   MkAwkernelSchedTraceAcceptanceState _ _ _ _ _ astas_blocked0 ->
    astas_blocked0}

initial_sched_trace_acceptance_state :: AwkernelSchedTraceAcceptanceState
initial_sched_trace_acceptance_state =
  MkAwkernelSchedTraceAcceptanceState Prelude.False None Nil Nil Nil Nil

sched_trace_step_start :: AwkernelTaskTraceSummary -> AwkernelSchedTraceEntry
                          -> Option AwkernelSchedTraceAcceptanceState
sched_trace_step_start summary entry =
  case atts_root_task summary of {
   Some root ->
    case sched_trace_is_wakeup root entry of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None Nil Nil Nil Nil);
     Prelude.False -> None};
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
    case (Prelude.&&)
           ((Prelude.&&) (sched_trace_is_wakeup j entry)
             (job_list_contains j known))
           (Prelude.not (job_list_contains j (astas_completed st))) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      (astas_selected st) (astas_dispatched st) (astas_completed st)
      (astas_ready_targets st) (remove_job j (astas_blocked st)));
     Prelude.False -> None}}
  in
  let {
   try_block_job = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&) (sched_trace_is_block j entry)
               (job_list_contains j known))
             (Prelude.not (job_list_contains j (astas_completed st))))
           (Prelude.not (job_list_contains j (astas_blocked st))) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None (astas_dispatched st) (astas_completed st)
      (astas_ready_targets st) (add_job_once j (astas_blocked st)));
     Prelude.False -> None}}
  in
  let {
   try_choose_job = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&)
               ((Prelude.&&) (sched_trace_is_choose j entry)
                 (job_list_contains j known))
               (Prelude.not (job_list_contains j (astas_completed st))))
             (Prelude.not (job_list_contains j (astas_blocked st))))
           (option_job_eqb (astas_selected st) None) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      (Some j) (astas_dispatched st) (astas_completed st)
      (astas_ready_targets st) (astas_blocked st));
     Prelude.False -> None}}
  in
  let {
   try_spurious_dispatch_job = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&)
               ((Prelude.&&) (sched_trace_is_dispatch j entry)
                 (option_job_eqb (astas_selected st) (Some j)))
               (job_list_contains j known))
             (Prelude.not (job_list_contains j (astas_completed st))))
           (task_trace_blocked_at summary (aste_event_id entry) j) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None (astas_dispatched st) (astas_completed st)
      (astas_ready_targets st) (astas_blocked st));
     Prelude.False -> None}}
  in
  let {
   try_dispatch_job = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&) (sched_trace_is_dispatch j entry)
               (option_job_eqb (astas_selected st) (Some j)))
             (Prelude.not (job_list_contains j (astas_blocked st))))
           (Prelude.not
             (task_trace_blocked_at summary (aste_event_id entry) j)) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None (add_job_once j (astas_dispatched st)) (astas_completed st)
      (astas_ready_targets st) (astas_blocked st));
     Prelude.False -> None}}
  in
  let {
   try_join_target_ready = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&) (sched_trace_is_join_target_ready j entry)
               (job_list_contains j known))
             (job_list_contains j ready_targets))
           (Prelude.not (job_list_contains j (astas_ready_targets st))) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None (astas_dispatched st) (astas_completed st)
      (add_job_once j (astas_ready_targets st)) (astas_blocked st));
     Prelude.False -> None}}
  in
  let {
   try_complete_job = \j ->
    case (Prelude.&&)
           ((Prelude.&&)
             ((Prelude.&&)
               ((Prelude.&&)
                 ((Prelude.&&) (sched_trace_is_complete j entry)
                   (job_list_contains j (astas_dispatched st)))
                 (Prelude.not (job_list_contains j (astas_completed st))))
               (Prelude.not (job_list_contains j (astas_blocked st))))
             (Prelude.not
               (task_trace_blocked_at summary (aste_event_id entry) j)))
           (all_dependencies_ready j deps (astas_ready_targets st)) of {
     Prelude.True -> Some (MkAwkernelSchedTraceAcceptanceState Prelude.True
      None (astas_dispatched st) (add_job_once j (astas_completed st))
      (astas_ready_targets st) (astas_blocked st));
     Prelude.False -> None}}
  in
  case sched_trace_is_stutter entry of {
   Prelude.True -> Some st;
   Prelude.False ->
    case first_some try_wakeup_job known of {
     Some st' -> Some st';
     None ->
      case first_some try_block_job known of {
       Some st' -> Some st';
       None ->
        case first_some try_choose_job known of {
         Some st' -> Some st';
         None ->
          case first_some try_spurious_dispatch_job known of {
           Some st' -> Some st';
           None ->
            case first_some try_dispatch_job known of {
             Some st' -> Some st';
             None ->
              case first_some try_join_target_ready known of {
               Some st' -> Some st';
               None -> first_some try_complete_job known}}}}}}}

sched_trace_step :: AwkernelTaskTraceSummary ->
                    AwkernelSchedTraceAcceptanceState ->
                    AwkernelSchedTraceEntry -> Option
                    AwkernelSchedTraceAcceptanceState
sched_trace_step summary st entry =
  case astas_started st of {
   Prelude.True -> sched_trace_step_after_start summary st entry;
   Prelude.False -> sched_trace_step_start summary entry}

accept_sched_trace_from :: AwkernelTaskTraceSummary ->
                           AwkernelSchedTraceAcceptanceState -> (List
                           AwkernelSchedTraceEntry) -> Prelude.Bool
accept_sched_trace_from summary st sched_trace =
  case sched_trace of {
   Nil ->
    case atts_root_task summary of {
     Some root -> job_list_contains root (astas_completed st);
     None -> Prelude.False};
   Cons entry sched_trace' ->
    case sched_trace_step summary st entry of {
     Some st' -> accept_sched_trace_from summary st' sched_trace';
     None -> Prelude.False}}

sched_trace_family_member :: AwkernelTaskTraceSummary -> (List
                             AwkernelSchedTraceEntry) -> Prelude.Bool
sched_trace_family_member summary sched_trace =
  accept_sched_trace_from summary initial_sched_trace_acceptance_state
    sched_trace

awk_workload_accepts_sched_trace :: (List AwkernelTaskTraceEntry) -> (List
                                    AwkernelSchedTraceEntry) -> Prelude.Bool
awk_workload_accepts_sched_trace task_trace sched_trace =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary -> sched_trace_family_member summary sched_trace;
   None -> Prelude.False}

empty_sched_trace_entry :: AwkernelSchedTraceEntry
empty_sched_trace_entry =
  MkAwkernelSchedTraceEntry 0 0 EvStutter None Nil Prelude.False None Nil Nil
    Nil

min_metric_job :: (JobId -> Z) -> (List JobId) -> Option JobId
min_metric_job metric l =
  case l of {
   Nil -> None;
   Cons j rest ->
    case min_metric_job metric rest of {
     Some j' ->
      case leb (metric j) (metric j') of {
       Prelude.True -> Some j;
       Prelude.False -> Some j'};
     None -> Some j}}

choose_min_metric :: (JobId -> Z) -> (JobId -> Job) -> Prelude.Integer ->
                     Schedule -> Time -> (List JobId) -> Option JobId
choose_min_metric metric jobs m sched t candidates =
  min_metric_job metric
    (filter (\j -> eligibleb jobs m sched j t) candidates)

choose_top_m_by_metric :: Prelude.Integer -> (JobId -> Z) -> (JobId -> Job)
                          -> Prelude.Integer -> Schedule -> Time -> (List
                          JobId) -> List JobId
choose_top_m_by_metric k metric jobs m sched t candidates =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Nil)
    (\k' ->
    case choose_min_metric metric jobs m sched t candidates of {
     Some j -> Cons j
      (choose_top_m_by_metric k' metric jobs m sched t
        (remove (Prelude.==) j candidates));
     None -> Nil})
    k

make_metric_top_m_algorithm :: ((JobId -> Job) -> JobId -> Z) ->
                               GenericTopMSchedulingAlgorithm
make_metric_top_m_algorithm metric_of_jobs jobs m sched t cands =
  choose_top_m_by_metric m (metric_of_jobs jobs) jobs m sched t cands

global_edf_metric_of_jobs :: (JobId -> Job) -> JobId -> Z
global_edf_metric_of_jobs jobs j =
  of_nat (job_abs_deadline (jobs j))

global_edf_top_m_spec :: GenericTopMSchedulingAlgorithm
global_edf_top_m_spec =
  make_metric_top_m_algorithm global_edf_metric_of_jobs

fifo_eligible_candidates :: (JobId -> Job) -> Prelude.Integer -> Schedule ->
                            Time -> (List JobId) -> List JobId
fifo_eligible_candidates jobs m sched t candidates =
  filter (\j -> eligibleb jobs m sched j t) (nodup (Prelude.==) candidates)

choose_top_m_fifo :: (JobId -> Job) -> Prelude.Integer -> Schedule -> Time ->
                     (List JobId) -> List JobId
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
   Prelude.True -> xs;
   Prelude.False -> app xs (Cons j Nil)}

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

sched_trace_global_fifo_rowb :: AwkernelSchedTraceEntry -> Prelude.Bool
sched_trace_global_fifo_rowb entry =
  case aste_event entry of {
   EvChoose cpu j ->
    (Prelude.&&)
      ((Prelude.&&) ((Prelude.==) (aste_cpu entry) (Prelude.succ 0))
        ((Prelude.==) cpu (Prelude.succ 0)))
      (option_job_eqb (sched_trace_fifo_head entry) (Some j));
   _ -> Prelude.True}

sched_trace_global_fifo_checkb :: (List AwkernelSchedTraceEntry) ->
                                  Prelude.Bool
sched_trace_global_fifo_checkb sched_trace =
  case sched_trace of {
   Nil -> Prelude.True;
   Cons entry sched_trace' ->
    (Prelude.&&) (sched_trace_global_fifo_rowb entry)
      (sched_trace_global_fifo_checkb sched_trace')}

first_non_fifo_sched_trace_index_from :: Prelude.Integer -> (List
                                         AwkernelSchedTraceEntry) -> Option
                                         Prelude.Integer
first_non_fifo_sched_trace_index_from n sched_trace =
  case sched_trace of {
   Nil -> None;
   Cons entry sched_trace' ->
    case sched_trace_global_fifo_rowb entry of {
     Prelude.True ->
      first_non_fifo_sched_trace_index_from (Prelude.succ n) sched_trace';
     Prelude.False -> Some n}}

first_non_fifo_sched_trace_index :: (List AwkernelSchedTraceEntry) -> Option
                                    Prelude.Integer
first_non_fifo_sched_trace_index sched_trace =
  first_non_fifo_sched_trace_index_from 0 sched_trace

awk_workload_accepts_global_fifo_sched_trace :: (List AwkernelTaskTraceEntry)
                                                -> (List
                                                AwkernelSchedTraceEntry) ->
                                                Prelude.Bool
awk_workload_accepts_global_fifo_sched_trace task_trace sched_trace =
  (Prelude.&&)
    ((Prelude.&&) (awk_workload_accepts_sched_trace task_trace sched_trace)
      (task_trace_all_global_fifo_policyb task_trace))
    (sched_trace_global_fifo_checkb sched_trace)

job_list_eqb :: (List JobId) -> (List JobId) -> Prelude.Bool
job_list_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> Prelude.True;
           Cons _ _ -> Prelude.False};
   Cons x xs' ->
    case ys of {
     Nil -> Prelude.False;
     Cons y ys' -> (Prelude.&&) ((Prelude.==) x y) (job_list_eqb xs' ys')}}

task_trace_blocks_at :: (List AwkernelTaskTraceEntry) -> Prelude.Integer ->
                        Prelude.Integer -> Prelude.Bool
task_trace_blocks_at task_trace event_id task_id =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary -> task_trace_blocked_at summary event_id task_id;
   None -> Prelude.False}

workload_scheduler_relation_candidates :: (List AwkernelTaskTraceEntry) ->
                                          AwkernelSchedTraceEntry -> List
                                          JobId
workload_scheduler_relation_candidates task_trace entry =
  case aste_event entry of {
   EvChoose cpu j ->
    case (Prelude.&&) ((Prelude.==) cpu (Prelude.succ 0))
           (Prelude.not
             (task_trace_blocks_at task_trace (aste_event_id entry) j)) of {
     Prelude.True -> sched_trace_fifo_candidates entry;
     Prelude.False -> Nil};
   _ -> Nil}

workload_scheduler_relation_choice :: (List AwkernelTaskTraceEntry) ->
                                      AwkernelSchedTraceEntry -> List
                                      JobId
workload_scheduler_relation_choice task_trace entry =
  case aste_event entry of {
   EvChoose cpu j ->
    case (Prelude.&&) ((Prelude.==) cpu (Prelude.succ 0))
           (Prelude.not
             (task_trace_blocks_at task_trace (aste_event_id entry) j)) of {
     Prelude.True -> Cons j Nil;
     Prelude.False -> Nil};
   _ -> Nil}

workload_scheduler_relation_schedule :: (List AwkernelTaskTraceEntry) ->
                                        (List AwkernelSchedTraceEntry) ->
                                        Schedule
workload_scheduler_relation_schedule task_trace sched_trace t c =
  case ltb c (Prelude.succ 0) of {
   Prelude.True ->
    nth_error
      (workload_scheduler_relation_choice task_trace
        (nth t sched_trace empty_sched_trace_entry))
      c;
   Prelude.False -> None}

task_trace_has_completeb :: JobId -> (List AwkernelTaskTraceEntry) ->
                            Prelude.Bool
task_trace_has_completeb task_id task_trace =
  case task_trace of {
   Nil -> Prelude.False;
   Cons entry task_trace' ->
    case atte_kind entry of {
     LkComplete ->
      (Prelude.||) ((Prelude.==) (atte_subject entry) task_id)
        (task_trace_has_completeb task_id task_trace');
     _ -> task_trace_has_completeb task_id task_trace'}}

count_scheduler_relation_service :: (List AwkernelTaskTraceEntry) -> JobId ->
                                    (List AwkernelSchedTraceEntry) ->
                                    Prelude.Integer
count_scheduler_relation_service task_trace task_id sched_trace =
  case sched_trace of {
   Nil -> 0;
   Cons entry sched_trace' ->
    let {
     rest = count_scheduler_relation_service task_trace task_id sched_trace'}
    in
    case workload_scheduler_relation_choice task_trace entry of {
     Nil -> rest;
     Cons j l ->
      case l of {
       Nil ->
        case (Prelude.==) j task_id of {
         Prelude.True -> Prelude.succ rest;
         Prelude.False -> rest};
       Cons _ _ -> rest}}}

first_scheduler_visible_index_from :: (List AwkernelTaskTraceEntry) ->
                                      Prelude.Integer -> Prelude.Integer ->
                                      (List AwkernelSchedTraceEntry) ->
                                      Option Prelude.Integer
first_scheduler_visible_index_from task_trace task_id n sched_trace =
  case sched_trace of {
   Nil -> None;
   Cons entry sched_trace' ->
    case job_list_contains task_id
           (workload_scheduler_relation_candidates task_trace entry) of {
     Prelude.True -> Some n;
     Prelude.False ->
      first_scheduler_visible_index_from task_trace task_id (Prelude.succ n)
        sched_trace'}}

first_scheduler_visible_index :: (List AwkernelTaskTraceEntry) -> JobId ->
                                 (List AwkernelSchedTraceEntry) -> Option
                                 Prelude.Integer
first_scheduler_visible_index task_trace task_id sched_trace =
  first_scheduler_visible_index_from task_trace task_id 0 sched_trace

reconstructed_scheduler_relation_release :: (List AwkernelTaskTraceEntry) ->
                                            JobId -> (List
                                            AwkernelSchedTraceEntry) ->
                                            Prelude.Integer
reconstructed_scheduler_relation_release task_trace task_id sched_trace =
  case first_scheduler_visible_index task_trace task_id sched_trace of {
   Some t -> t;
   None -> 0}

reconstructed_scheduler_relation_cost :: (List AwkernelTaskTraceEntry) ->
                                         (List AwkernelSchedTraceEntry) ->
                                         JobId -> Prelude.Integer
reconstructed_scheduler_relation_cost task_trace sched_trace task_id =
  let {
   service = count_scheduler_relation_service task_trace task_id sched_trace}
  in
  case task_trace_has_completeb task_id task_trace of {
   Prelude.True ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.succ 0)
      (\_ -> service)
      service;
   Prelude.False -> Prelude.succ service}

reconstructed_scheduler_relation_abs_deadline :: (List
                                                 AwkernelTaskTraceEntry) ->
                                                 (List
                                                 AwkernelSchedTraceEntry) ->
                                                 JobId -> Prelude.Integer
reconstructed_scheduler_relation_abs_deadline task_trace sched_trace task_id =
  (Prelude.+)
    ((Prelude.+)
      (reconstructed_scheduler_relation_release task_trace task_id
        sched_trace)
      (reconstructed_scheduler_relation_cost task_trace sched_trace task_id))
    (length sched_trace)

workload_scheduler_relation_jobs :: (List AwkernelTaskTraceEntry) -> (List
                                    AwkernelSchedTraceEntry) -> JobId -> Job
workload_scheduler_relation_jobs task_trace sched_trace task_id =
  MkJob task_id 0
    (reconstructed_scheduler_relation_release task_trace task_id sched_trace)
    (reconstructed_scheduler_relation_cost task_trace sched_trace task_id)
    (reconstructed_scheduler_relation_abs_deadline task_trace sched_trace
      task_id)
    (\_ -> Prelude.False)

workload_global_fifo_scheduler_relation_rowb :: (List AwkernelTaskTraceEntry)
                                                -> (List
                                                AwkernelSchedTraceEntry) ->
                                                Time ->
                                                AwkernelSchedTraceEntry ->
                                                Prelude.Bool
workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t entry =
  job_list_eqb
    (choose_top_m global_fifo_top_m_spec
      (workload_scheduler_relation_jobs task_trace sched_trace) (Prelude.succ
      0) (workload_scheduler_relation_schedule task_trace sched_trace) t
      (workload_scheduler_relation_candidates task_trace entry))
    (workload_scheduler_relation_choice task_trace entry)

sched_trace_global_fifo_scheduler_relation_check_from :: (List
                                                         AwkernelTaskTraceEntry)
                                                         -> (List
                                                         AwkernelSchedTraceEntry)
                                                         -> Prelude.Integer
                                                         -> (List
                                                         AwkernelSchedTraceEntry)
                                                         -> Prelude.Bool
sched_trace_global_fifo_scheduler_relation_check_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> Prelude.True;
   Cons entry remaining' ->
    (Prelude.&&)
      (workload_global_fifo_scheduler_relation_rowb task_trace sched_trace t
        entry)
      (sched_trace_global_fifo_scheduler_relation_check_from task_trace
        sched_trace (Prelude.succ t) remaining')}

sched_trace_global_fifo_scheduler_relation_checkb :: (List
                                                     AwkernelTaskTraceEntry)
                                                     -> (List
                                                     AwkernelSchedTraceEntry)
                                                     -> Prelude.Bool
sched_trace_global_fifo_scheduler_relation_checkb task_trace sched_trace =
  sched_trace_global_fifo_scheduler_relation_check_from task_trace
    sched_trace 0 sched_trace

first_non_scheduler_relation_sched_trace_index_from :: (List
                                                       AwkernelTaskTraceEntry)
                                                       -> (List
                                                       AwkernelSchedTraceEntry)
                                                       -> Prelude.Integer ->
                                                       (List
                                                       AwkernelSchedTraceEntry)
                                                       -> Option
                                                       Prelude.Integer
first_non_scheduler_relation_sched_trace_index_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> None;
   Cons entry remaining' ->
    case workload_global_fifo_scheduler_relation_rowb task_trace sched_trace
           t entry of {
     Prelude.True ->
      first_non_scheduler_relation_sched_trace_index_from task_trace
        sched_trace (Prelude.succ t) remaining';
     Prelude.False -> Some t}}

first_non_scheduler_relation_sched_trace_index :: (List
                                                  AwkernelTaskTraceEntry) ->
                                                  (List
                                                  AwkernelSchedTraceEntry) ->
                                                  Option Prelude.Integer
first_non_scheduler_relation_sched_trace_index task_trace sched_trace =
  first_non_scheduler_relation_sched_trace_index_from task_trace sched_trace
    0 sched_trace

awk_workload_accepts_global_fifo_scheduler_relation_sched_trace :: (List
                                                                   AwkernelTaskTraceEntry)
                                                                   -> (List
                                                                   AwkernelSchedTraceEntry)
                                                                   ->
                                                                   Prelude.Bool
awk_workload_accepts_global_fifo_scheduler_relation_sched_trace task_trace sched_trace =
  (Prelude.&&)
    ((Prelude.&&) (awk_workload_accepts_sched_trace task_trace sched_trace)
      (task_trace_all_global_fifo_policyb task_trace))
    (sched_trace_global_fifo_scheduler_relation_checkb task_trace
      sched_trace)

task_policy_table_lookup :: JobId -> (List (Prod JobId AwkernelTaskPolicy))
                            -> Option AwkernelTaskPolicy
task_policy_table_lookup task_id policies =
  case policies of {
   Nil -> None;
   Cons p policies' ->
    case p of {
     Pair policy_task policy ->
      case (Prelude.==) policy_task task_id of {
       Prelude.True -> Some policy;
       Prelude.False -> task_policy_table_lookup task_id policies'}}}

task_trace_summary_policy_at :: AwkernelTaskTraceSummary -> JobId -> Option
                                AwkernelTaskPolicy
task_trace_summary_policy_at summary task_id =
  task_policy_table_lookup task_id (atts_task_policies summary)

sched_trace_candidate_is_edfb :: AwkernelTaskTraceSummary -> JobId ->
                                 Prelude.Bool
sched_trace_candidate_is_edfb summary task_id =
  case task_trace_summary_policy_at summary task_id of {
   Some policy -> task_policy_global_edf_supportedb policy;
   None -> Prelude.False}

filter_sched_trace_edf_candidates :: AwkernelTaskTraceSummary -> (List
                                     JobId) -> List JobId
filter_sched_trace_edf_candidates summary candidates =
  case candidates of {
   Nil -> Nil;
   Cons j candidates' ->
    case sched_trace_candidate_is_edfb summary j of {
     Prelude.True -> Cons j
      (filter_sched_trace_edf_candidates summary candidates');
     Prelude.False -> filter_sched_trace_edf_candidates summary candidates'}}

sched_trace_edf_deadline_presentb :: AwkernelTaskTraceSummary ->
                                     AwkernelSchedTraceEntry -> JobId ->
                                     Prelude.Bool
sched_trace_edf_deadline_presentb summary entry task_id =
  case task_trace_edf_deadline_at summary (aste_event_id entry) task_id of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

sched_trace_edf_candidate_deadline_validb :: AwkernelTaskTraceSummary ->
                                             AwkernelSchedTraceEntry -> JobId
                                             -> Prelude.Bool
sched_trace_edf_candidate_deadline_validb summary entry task_id =
  (Prelude.||) (Prelude.not (sched_trace_candidate_is_edfb summary task_id))
    (sched_trace_edf_deadline_presentb summary entry task_id)

sched_trace_edf_candidate_deadlines_validb :: AwkernelTaskTraceSummary ->
                                              AwkernelSchedTraceEntry ->
                                              (List JobId) -> Prelude.Bool
sched_trace_edf_candidate_deadlines_validb summary entry candidates =
  case candidates of {
   Nil -> Prelude.True;
   Cons j candidates' ->
    (Prelude.&&) (sched_trace_edf_candidate_deadline_validb summary entry j)
      (sched_trace_edf_candidate_deadlines_validb summary entry candidates')}

workload_edf_fifo_scheduler_relation_jobs :: AwkernelTaskTraceSummary ->
                                             (List AwkernelTaskTraceEntry) ->
                                             (List AwkernelSchedTraceEntry)
                                             -> AwkernelSchedTraceEntry ->
                                             JobId -> Job
workload_edf_fifo_scheduler_relation_jobs summary task_trace sched_trace entry task_id =
  MkJob task_id 0
    (reconstructed_scheduler_relation_release task_trace task_id sched_trace)
    (reconstructed_scheduler_relation_cost task_trace sched_trace task_id)
    (case task_trace_edf_deadline_at summary (aste_event_id entry) task_id of {
      Some deadline -> deadline;
      None ->
       reconstructed_scheduler_relation_abs_deadline task_trace sched_trace
         task_id})
    (\_ -> Prelude.False)

workload_edf_fifo_scheduler_relation_row_choice :: (List
                                                   AwkernelTaskTraceEntry) ->
                                                   (List
                                                   AwkernelSchedTraceEntry)
                                                   ->
                                                   AwkernelTaskTraceSummary
                                                   -> Time ->
                                                   AwkernelSchedTraceEntry ->
                                                   List JobId
workload_edf_fifo_scheduler_relation_row_choice task_trace sched_trace summary t entry =
  let {candidates = workload_scheduler_relation_candidates task_trace entry}
  in
  case sched_trace_edf_candidate_deadlines_validb summary entry candidates of {
   Prelude.True ->
    case filter_sched_trace_edf_candidates summary candidates of {
     Nil ->
      choose_top_m global_fifo_top_m_spec
        (workload_scheduler_relation_jobs task_trace sched_trace)
        (Prelude.succ 0)
        (workload_scheduler_relation_schedule task_trace sched_trace) t
        candidates;
     Cons j l ->
      choose_top_m global_edf_top_m_spec
        (workload_edf_fifo_scheduler_relation_jobs summary task_trace
          sched_trace entry)
        (Prelude.succ 0)
        (workload_scheduler_relation_schedule task_trace sched_trace) t (Cons
        j l)};
   Prelude.False -> Nil}

workload_edf_fifo_scheduler_relation_rowb :: (List AwkernelTaskTraceEntry) ->
                                             (List AwkernelSchedTraceEntry)
                                             -> Time ->
                                             AwkernelSchedTraceEntry ->
                                             Prelude.Bool
workload_edf_fifo_scheduler_relation_rowb task_trace sched_trace t entry =
  case summarize_task_trace initial_task_trace_summary task_trace of {
   Some summary ->
    (Prelude.&&)
      (sched_trace_edf_candidate_deadlines_validb summary entry
        (workload_scheduler_relation_candidates task_trace entry))
      (job_list_eqb
        (workload_edf_fifo_scheduler_relation_row_choice task_trace
          sched_trace summary t entry)
        (workload_scheduler_relation_choice task_trace entry));
   None -> Prelude.False}

sched_trace_edf_fifo_scheduler_relation_check_from :: (List
                                                      AwkernelTaskTraceEntry)
                                                      -> (List
                                                      AwkernelSchedTraceEntry)
                                                      -> Prelude.Integer ->
                                                      (List
                                                      AwkernelSchedTraceEntry)
                                                      -> Prelude.Bool
sched_trace_edf_fifo_scheduler_relation_check_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> Prelude.True;
   Cons entry remaining' ->
    (Prelude.&&)
      (workload_edf_fifo_scheduler_relation_rowb task_trace sched_trace t
        entry)
      (sched_trace_edf_fifo_scheduler_relation_check_from task_trace
        sched_trace (Prelude.succ t) remaining')}

sched_trace_edf_fifo_scheduler_relation_checkb :: (List
                                                  AwkernelTaskTraceEntry) ->
                                                  (List
                                                  AwkernelSchedTraceEntry) ->
                                                  Prelude.Bool
sched_trace_edf_fifo_scheduler_relation_checkb task_trace sched_trace =
  sched_trace_edf_fifo_scheduler_relation_check_from task_trace sched_trace 0
    sched_trace

first_non_edf_fifo_scheduler_relation_sched_trace_index_from :: (List
                                                                AwkernelTaskTraceEntry)
                                                                -> (List
                                                                AwkernelSchedTraceEntry)
                                                                ->
                                                                Prelude.Integer
                                                                -> (List
                                                                AwkernelSchedTraceEntry)
                                                                -> Option
                                                                Prelude.Integer
first_non_edf_fifo_scheduler_relation_sched_trace_index_from task_trace sched_trace t remaining =
  case remaining of {
   Nil -> None;
   Cons entry remaining' ->
    case workload_edf_fifo_scheduler_relation_rowb task_trace sched_trace t
           entry of {
     Prelude.True ->
      first_non_edf_fifo_scheduler_relation_sched_trace_index_from task_trace
        sched_trace (Prelude.succ t) remaining';
     Prelude.False -> Some t}}

first_non_edf_fifo_scheduler_relation_sched_trace_index :: (List
                                                           AwkernelTaskTraceEntry)
                                                           -> (List
                                                           AwkernelSchedTraceEntry)
                                                           -> Option
                                                           Prelude.Integer
first_non_edf_fifo_scheduler_relation_sched_trace_index task_trace sched_trace =
  first_non_edf_fifo_scheduler_relation_sched_trace_index_from task_trace
    sched_trace 0 sched_trace

awk_workload_accepts_edf_fifo_scheduler_relation_sched_trace :: (List
                                                                AwkernelTaskTraceEntry)
                                                                -> (List
                                                                AwkernelSchedTraceEntry)
                                                                ->
                                                                Prelude.Bool
awk_workload_accepts_edf_fifo_scheduler_relation_sched_trace task_trace sched_trace =
  (Prelude.&&)
    ((Prelude.&&) (awk_workload_accepts_sched_trace task_trace sched_trace)
      (task_trace_all_edf_fifo_policyb task_trace))
    (sched_trace_edf_fifo_scheduler_relation_checkb task_trace sched_trace)

