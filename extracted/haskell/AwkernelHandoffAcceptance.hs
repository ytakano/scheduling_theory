module AwkernelHandoffAcceptance where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

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

data AwkernelState =
   MkAwkernelState (CPU -> Option JobId) (List JobId) (CPU -> Bool) (CPU ->
                                                                    Option
                                                                    JobId)

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

awk_baseline_state0 :: AwkernelState
awk_baseline_state0 =
  MkAwkernelState (\_ -> None) Nil (\_ -> False) (\_ -> None)

awk_baseline_state1 :: AwkernelState
awk_baseline_state1 =
  MkAwkernelState (\_ -> None) (Cons (S O) Nil) (\_ -> False) (\_ -> None)

awk_baseline_state3 :: AwkernelState
awk_baseline_state3 =
  MkAwkernelState (\c ->
    case eqb0 c (S O) of {
     True -> Some (S O);
     False -> None}) Nil (\_ -> False) (\_ -> None)

awk_baseline_state4 :: AwkernelState
awk_baseline_state4 =
  MkAwkernelState (\_ -> None) Nil (\c -> eqb0 c (S O)) (\_ -> None)

data AwkernelHandoffState =
   MkAwkernelHandoffState AwkernelState Nat

awk_handoff_phase :: AwkernelHandoffState -> Nat
awk_handoff_phase a =
  case a of {
   MkAwkernelHandoffState _ awk_handoff_phase0 -> awk_handoff_phase0}

awk_handoff_state0 :: AwkernelHandoffState
awk_handoff_state0 =
  MkAwkernelHandoffState awk_baseline_state0 O

awk_handoff_state1 :: AwkernelHandoffState
awk_handoff_state1 =
  MkAwkernelHandoffState awk_baseline_state1 (S O)

awk_handoff_request_visible :: AwkernelState
awk_handoff_request_visible =
  MkAwkernelState (\_ -> None) (Cons (S O) Nil) (\c -> eqb0 c (S O)) (\_ ->
    None)

awk_handoff_state2 :: AwkernelHandoffState
awk_handoff_state2 =
  MkAwkernelHandoffState awk_handoff_request_visible (S (S O))

awk_handoff_state3 :: AwkernelHandoffState
awk_handoff_state3 =
  MkAwkernelHandoffState awk_handoff_request_visible (S (S (S O)))

awk_handoff_choose_visible :: AwkernelState
awk_handoff_choose_visible =
  MkAwkernelState (\_ -> None) (Cons (S O) Nil) (\c -> eqb0 c (S O)) (\c ->
    case eqb0 c (S O) of {
     True -> Some (S O);
     False -> None})

awk_handoff_state4 :: AwkernelHandoffState
awk_handoff_state4 =
  MkAwkernelHandoffState awk_handoff_choose_visible (S (S (S (S O))))

awk_handoff_state5 :: AwkernelHandoffState
awk_handoff_state5 =
  MkAwkernelHandoffState awk_baseline_state3 (S (S (S (S (S O)))))

awk_handoff_state6 :: AwkernelHandoffState
awk_handoff_state6 =
  MkAwkernelHandoffState awk_baseline_state4 (S (S (S (S (S (S O))))))

op_event_eqb :: OpEvent -> OpEvent -> Bool
op_event_eqb x y =
  case x of {
   EvWakeup j1 -> case y of {
                   EvWakeup j2 -> eqb0 j1 j2;
                   _ -> False};
   EvBlock j1 -> case y of {
                  EvBlock j2 -> eqb0 j1 j2;
                  _ -> False};
   EvComplete j1 -> case y of {
                     EvComplete j2 -> eqb0 j1 j2;
                     _ -> False};
   EvRequestResched c1 ->
    case y of {
     EvRequestResched c2 -> eqb0 c1 c2;
     _ -> False};
   EvHandleResched c1 ->
    case y of {
     EvHandleResched c2 -> eqb0 c1 c2;
     _ -> False};
   EvChoose c1 j1 ->
    case y of {
     EvChoose c2 j2 -> andb (eqb0 c1 c2) (eqb0 j1 j2);
     _ -> False};
   EvDispatch c1 j1 ->
    case y of {
     EvDispatch c2 j2 -> andb (eqb0 c1 c2) (eqb0 j1 j2);
     _ -> False};
   EvPreempt c1 old1 new1 ->
    case y of {
     EvPreempt c2 old2 new2 ->
      andb (andb (eqb0 c1 c2) (eqb0 old1 old2)) (eqb0 new1 new2);
     _ -> False};
   EvStutter -> case y of {
                 EvStutter -> True;
                 _ -> False};
   EvTick -> case y of {
              EvTick -> True;
              _ -> False}}

awk_handoff_row_wakeup :: AwkernelCapturedRow
awk_handoff_row_wakeup =
  MkAwkernelCapturedRow O (EvWakeup (S O)) None (Cons (S O) Nil) False None

awk_handoff_row_request_resched :: AwkernelCapturedRow
awk_handoff_row_request_resched =
  MkAwkernelCapturedRow (S O) (EvRequestResched (S O)) None (Cons (S O) Nil)
    True None

awk_handoff_row_handle_resched :: AwkernelCapturedRow
awk_handoff_row_handle_resched =
  MkAwkernelCapturedRow (S O) (EvHandleResched (S O)) None (Cons (S O) Nil)
    True None

awk_handoff_row_choose :: AwkernelCapturedRow
awk_handoff_row_choose =
  MkAwkernelCapturedRow (S O) (EvChoose (S O) (S O)) None (Cons (S O) Nil)
    True (Some (S O))

awk_handoff_row_dispatch :: AwkernelCapturedRow
awk_handoff_row_dispatch =
  MkAwkernelCapturedRow (S O) (EvDispatch (S O) (S O)) (Some (S O)) Nil False
    None

awk_handoff_row_complete :: AwkernelCapturedRow
awk_handoff_row_complete =
  MkAwkernelCapturedRow (S O) (EvComplete (S O)) None Nil True None

option_job_eqb :: (Option JobId) -> (Option JobId) -> Bool
option_job_eqb x y =
  case x of {
   Some j1 -> case y of {
               Some j2 -> eqb0 j1 j2;
               None -> False};
   None -> case y of {
            Some _ -> False;
            None -> True}}

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

captured_row_eqb :: AwkernelCapturedRow -> AwkernelCapturedRow -> Bool
captured_row_eqb x y =
  andb
    (andb
      (andb
        (andb
          (andb (eqb0 (acr_cpu x) (acr_cpu y))
            (op_event_eqb (acr_event x) (acr_event y)))
          (option_job_eqb (acr_current x) (acr_current y)))
        (job_list_eqb (acr_runnable x) (acr_runnable y)))
      (eqb (acr_need_resched x) (acr_need_resched y)))
    (option_job_eqb (acr_dispatch_target x) (acr_dispatch_target y))

awk_handoff_row_step_next :: AwkernelHandoffState -> AwkernelCapturedRow ->
                             Option AwkernelHandoffState
awk_handoff_row_step_next st row =
  case captured_row_eqb row awk_handoff_row_wakeup of {
   True ->
    case awk_handoff_phase st of {
     O -> Some awk_handoff_state1;
     S _ -> None};
   False ->
    case captured_row_eqb row awk_handoff_row_request_resched of {
     True ->
      case awk_handoff_phase st of {
       O -> None;
       S n -> case n of {
               O -> Some awk_handoff_state2;
               S _ -> None}};
     False ->
      case captured_row_eqb row awk_handoff_row_handle_resched of {
       True ->
        case awk_handoff_phase st of {
         O -> None;
         S n ->
          case n of {
           O -> None;
           S n0 -> case n0 of {
                    O -> Some awk_handoff_state3;
                    S _ -> None}}};
       False ->
        case captured_row_eqb row awk_handoff_row_choose of {
         True ->
          case awk_handoff_phase st of {
           O -> None;
           S n ->
            case n of {
             O -> None;
             S n0 ->
              case n0 of {
               O -> None;
               S n1 ->
                case n1 of {
                 O -> Some awk_handoff_state4;
                 S _ -> None}}}};
         False ->
          case captured_row_eqb row awk_handoff_row_dispatch of {
           True ->
            case awk_handoff_phase st of {
             O -> None;
             S n ->
              case n of {
               O -> None;
               S n0 ->
                case n0 of {
                 O -> None;
                 S n1 ->
                  case n1 of {
                   O -> None;
                   S n2 ->
                    case n2 of {
                     O -> Some awk_handoff_state5;
                     S _ -> None}}}}};
           False ->
            case captured_row_eqb row awk_handoff_row_complete of {
             True ->
              case awk_handoff_phase st of {
               O -> None;
               S n ->
                case n of {
                 O -> None;
                 S n0 ->
                  case n0 of {
                   O -> None;
                   S n1 ->
                    case n1 of {
                     O -> None;
                     S n2 ->
                      case n2 of {
                       O -> None;
                       S n3 ->
                        case n3 of {
                         O -> Some awk_handoff_state6;
                         S _ -> None}}}}}};
             False -> None}}}}}}

awk_handoff_generate_post_states_from :: AwkernelHandoffState -> (List
                                         AwkernelCapturedRow) -> Option
                                         (List AwkernelHandoffState)
awk_handoff_generate_post_states_from st rows =
  case rows of {
   Nil -> Some Nil;
   Cons row rows' ->
    case awk_handoff_row_step_next st row of {
     Some st' ->
      case awk_handoff_generate_post_states_from st' rows' of {
       Some states -> Some (Cons st' states);
       None -> None};
     None -> None}}

awk_handoff_generate_post_states :: (List AwkernelCapturedRow) -> Option
                                    (List AwkernelHandoffState)
awk_handoff_generate_post_states rows =
  awk_handoff_generate_post_states_from awk_handoff_state0 rows

awk_handoff_check_rows :: (List AwkernelCapturedRow) -> Option
                          (List AwkernelHandoffState)
awk_handoff_check_rows =
  awk_handoff_generate_post_states

awk_handoff_accepts_rows :: (List AwkernelCapturedRow) -> Bool
awk_handoff_accepts_rows rows =
  case awk_handoff_check_rows rows of {
   Some _ -> True;
   None -> False}

