module EDFInfiniteCertificateChecker where

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

data Prod a b =
   Pair a b

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb n' m'}}

even :: Nat -> Bool
even n =
  case n of {
   O -> True;
   S n0 -> case n0 of {
            O -> False;
            S n' -> even n'}}

divmod :: Nat -> Nat -> Nat -> Nat -> Prod Nat Nat
divmod x y q u =
  case x of {
   O -> Pair q u;
   S x' -> case u of {
            O -> divmod x' y (S q) y;
            S u' -> divmod x' y q u'}}

modulo :: Nat -> Nat -> Nat
modulo x y =
  case y of {
   O -> x;
   S y' -> sub y' (snd (divmod x y' O y'))}

div2 :: Nat -> Nat
div2 n =
  case n of {
   O -> O;
   S n0 -> case n0 of {
            O -> O;
            S n' -> S (div2 n')}}

type JobId = Nat

type TaskId = Nat

type Time = Nat

data Job =
   MkJob TaskId Nat Time Nat Time

job_task :: Job -> TaskId
job_task j =
  case j of {
   MkJob job_task0 _ _ _ _ -> job_task0}

job_index :: Job -> Nat
job_index j =
  case j of {
   MkJob _ job_index0 _ _ _ -> job_index0}

job_release :: Job -> Time
job_release j =
  case j of {
   MkJob _ _ job_release0 _ _ -> job_release0}

jobs_ex :: JobId -> Job
jobs_ex j =
  case even j of {
   True -> MkJob O (div2 j) (mul (S (S (S (S (S O))))) (div2 j)) (S O)
    (add (mul (S (S (S (S (S O))))) (div2 j)) (S (S O)));
   False -> MkJob (S O) (div2 j) (mul (S (S (S (S (S (S (S O))))))) (div2 j))
    (S O) (add (mul (S (S (S (S (S (S (S O))))))) (div2 j)) (S (S (S O))))}

data EDFInfiniteCertEx =
   Build_EDFInfiniteCertEx Time Time Time Time

cert_hyperperiod_ex :: EDFInfiniteCertEx -> Time
cert_hyperperiod_ex e =
  case e of {
   Build_EDFInfiniteCertEx cert_hyperperiod_ex0 _ _ _ -> cert_hyperperiod_ex0}

cert_task0_completion_delay_ex :: EDFInfiniteCertEx -> Time
cert_task0_completion_delay_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ cert_task0_completion_delay_ex0 _ _ ->
    cert_task0_completion_delay_ex0}

cert_task1_completion_delay_ex :: EDFInfiniteCertEx -> Time
cert_task1_completion_delay_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ _ cert_task1_completion_delay_ex0 _ ->
    cert_task1_completion_delay_ex0}

cert_task1_collision_completion_delay_ex :: EDFInfiniteCertEx -> Time
cert_task1_collision_completion_delay_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ _ _ cert_task1_collision_completion_delay_ex0 ->
    cert_task1_collision_completion_delay_ex0}

cert_ex :: EDFInfiniteCertEx
cert_ex =
  Build_EDFInfiniteCertEx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))) (S O) (S O) (S (S O))

check_edf_infinite_cert_ex :: EDFInfiniteCertEx -> Bool
check_edf_infinite_cert_ex c =
  andb
    (andb
      (andb
        (eqb (cert_hyperperiod_ex c) (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))
        (eqb (cert_task0_completion_delay_ex c) (S O)))
      (eqb (cert_task1_completion_delay_ex c) (S O)))
    (eqb (cert_task1_collision_completion_delay_ex c) (S (S O)))

cert_completion_target_time_ex :: EDFInfiniteCertEx -> JobId -> Time
cert_completion_target_time_ex c j =
  case job_task (jobs_ex j) of {
   O -> add (job_release (jobs_ex j)) (cert_task0_completion_delay_ex c);
   S n ->
    case n of {
     O ->
      case eqb (modulo (job_index (jobs_ex j)) (S (S (S (S (S O)))))) O of {
       True ->
        add (job_release (jobs_ex j))
          (cert_task1_collision_completion_delay_ex c);
       False ->
        add (job_release (jobs_ex j)) (cert_task1_completion_delay_ex c)};
     S _ -> O}}

