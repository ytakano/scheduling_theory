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

data Option a =
   Some a
 | None

data List a =
   Nil
 | Cons a (List a)

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

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

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb n' m'}}

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

even :: Nat -> Bool
even n =
  case n of {
   O -> True;
   S n0 -> case n0 of {
            O -> False;
            S n' -> even n'}}

div2 :: Nat -> Nat
div2 n =
  case n of {
   O -> O;
   S n0 -> case n0 of {
            O -> O;
            S n' -> S (div2 n')}}

seq :: Nat -> Nat -> List Nat
seq start len =
  case len of {
   O -> Nil;
   S len0 -> Cons start (seq (S start) len0)}

nth :: Nat -> (List a1) -> a1 -> a1
nth n l default0 =
  case n of {
   O -> case l of {
         Nil -> default0;
         Cons x _ -> x};
   S m -> case l of {
           Nil -> default0;
           Cons _ l' -> nth m l' default0}}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

type JobId = Nat

type TaskId = Nat

type CPU = Nat

type Time = Nat

data Job =
   MkJob TaskId Nat Time Nat Time

job_release :: Job -> Time
job_release j =
  case j of {
   MkJob _ _ job_release0 _ _ -> job_release0}

job_cost :: Job -> Nat
job_cost j =
  case j of {
   MkJob _ _ _ job_cost0 _ -> job_cost0}

job_abs_deadline :: Job -> Time
job_abs_deadline j =
  case j of {
   MkJob _ _ _ _ job_abs_deadline0 -> job_abs_deadline0}

type Schedule = Time -> CPU -> Option JobId

job_id_of_ex :: TaskId -> Nat -> JobId
job_id_of_ex tau k =
  case tau of {
   O -> mul (S (S O)) k;
   S n -> case n of {
           O -> S (mul (S (S O)) k);
           S _ -> O}}

jobs_ex :: JobId -> Job
jobs_ex j =
  case even j of {
   True -> MkJob O (div2 j) (mul (S (S (S (S (S O))))) (div2 j)) (S O)
    (add (mul (S (S (S (S (S O))))) (div2 j)) (S (S O)));
   False -> MkJob (S O) (div2 j) (mul (S (S (S (S (S (S (S O))))))) (div2 j))
    (S O) (add (mul (S (S (S (S (S (S (S O))))))) (div2 j)) (S (S (S O))))}

data EDFPrefixCertEx =
   Build_EDFPrefixCertEx Time (List (Option JobId))

cert_horizon_ex :: EDFPrefixCertEx -> Time
cert_horizon_ex e =
  case e of {
   Build_EDFPrefixCertEx cert_horizon_ex0 _ -> cert_horizon_ex0}

cert_slots_ex :: EDFPrefixCertEx -> List (Option JobId)
cert_slots_ex e =
  case e of {
   Build_EDFPrefixCertEx _ cert_slots_ex0 -> cert_slots_ex0}

data EDFInfiniteCertEx =
   Build_EDFInfiniteCertEx Time EDFPrefixCertEx Nat Nat

cert_period_ex :: EDFInfiniteCertEx -> Time
cert_period_ex e =
  case e of {
   Build_EDFInfiniteCertEx cert_period_ex0 _ _ _ -> cert_period_ex0}

cert_prefix_ex :: EDFInfiniteCertEx -> EDFPrefixCertEx
cert_prefix_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ cert_prefix_ex0 _ _ -> cert_prefix_ex0}

cert_task0_shift_ex :: EDFInfiniteCertEx -> Nat
cert_task0_shift_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ _ cert_task0_shift_ex0 _ -> cert_task0_shift_ex0}

cert_task1_shift_ex :: EDFInfiniteCertEx -> Nat
cert_task1_shift_ex e =
  case e of {
   Build_EDFInfiniteCertEx _ _ _ cert_task1_shift_ex0 -> cert_task1_shift_ex0}

cert_slots_ex_data :: List (Option JobId)
cert_slots_ex_data =
  Cons (Some O) (Cons (Some (S O)) (Cons None (Cons None (Cons None (Cons
    (Some (S (S O))) (Cons None (Cons (Some (S (S (S O)))) (Cons None (Cons
    None (Cons (Some (S (S (S (S O))))) (Cons None (Cons None (Cons None
    (Cons (Some (S (S (S (S (S O)))))) (Cons (Some (S (S (S (S (S (S O)))))))
    (Cons None (Cons None (Cons None (Cons None (Cons (Some (S (S (S (S (S (S
    (S (S O))))))))) (Cons (Some (S (S (S (S (S (S (S O)))))))) (Cons None
    (Cons None (Cons None (Cons (Some (S (S (S (S (S (S (S (S (S (S
    O))))))))))) (Cons None (Cons None (Cons (Some (S (S (S (S (S (S (S (S (S
    O)))))))))) (Cons None (Cons (Some (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))) (Cons None (Cons None (Cons None (Cons None (Cons (Some (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))) (Cons (Some (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))) (Cons None
    Nil)))))))))))))))))))))))))))))))))))))

cert_ex :: EDFInfiniteCertEx
cert_ex =
  Build_EDFInfiniteCertEx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))) (Build_EDFPrefixCertEx (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))
    cert_slots_ex_data) (S (S (S (S (S (S (S O))))))) (S (S (S (S (S O)))))

option_jobid_eqb :: (Option JobId) -> (Option JobId) -> Bool
option_jobid_eqb x y =
  case x of {
   Some j1 -> case y of {
               Some j2 -> eqb j1 j2;
               None -> False};
   None -> case y of {
            Some _ -> False;
            None -> True}}

certified_prefix_schedule_ex :: EDFPrefixCertEx -> Schedule
certified_prefix_schedule_ex p t cpu =
  case eqb cpu O of {
   True -> nth t (cert_slots_ex p) None;
   False -> None}

check_prefix_shape_ex :: EDFPrefixCertEx -> Bool
check_prefix_shape_ex p =
  andb
    (eqb (cert_horizon_ex p) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))
    (eqb (length (cert_slots_ex p)) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))

check_prefix_slots_match_ex :: EDFPrefixCertEx -> Bool
check_prefix_slots_match_ex p =
  forallb (\t ->
    option_jobid_eqb (nth t (cert_slots_ex p) None)
      (nth t cert_slots_ex_data None))
    (seq O (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))

check_prefix_edf_ex :: EDFPrefixCertEx -> Bool
check_prefix_edf_ex =
  check_prefix_slots_match_ex

certified_service_prefix_ex :: (List (Option JobId)) -> Nat -> Nat -> Nat
certified_service_prefix_ex slots j t =
  case t of {
   O -> O;
   S t' ->
    add (certified_service_prefix_ex slots j t')
      (case nth t' slots None of {
        Some j' -> case eqb j j' of {
                    True -> S O;
                    False -> O};
        None -> O})}

certified_completed_by_ex :: (List (Option JobId)) -> Nat -> Nat -> Bool
certified_completed_by_ex slots j t =
  leb (job_cost (jobs_ex j)) (certified_service_prefix_ex slots j t)

cert_base_jobs_ex :: List JobId
cert_base_jobs_ex =
  Cons (job_id_of_ex O O) (Cons (job_id_of_ex (S O) O) (Cons
    (job_id_of_ex O (S O)) (Cons (job_id_of_ex (S O) (S O)) (Cons
    (job_id_of_ex O (S (S O))) (Cons (job_id_of_ex (S O) (S (S O))) (Cons
    (job_id_of_ex O (S (S (S O)))) (Cons (job_id_of_ex (S O) (S (S (S O))))
    (Cons (job_id_of_ex O (S (S (S (S O))))) (Cons
    (job_id_of_ex (S O) (S (S (S (S O))))) (Cons
    (job_id_of_ex O (S (S (S (S (S O)))))) (Cons
    (job_id_of_ex (S O) (S (S (S (S (S O)))))) (Cons
    (job_id_of_ex O (S (S (S (S (S (S O))))))) (Cons
    (job_id_of_ex O (S (S (S (S (S (S (S O)))))))) Nil)))))))))))))

check_prefix_service_ex :: EDFPrefixCertEx -> Bool
check_prefix_service_ex p =
  forallb (\j ->
    certified_completed_by_ex (cert_slots_ex p) j (S
      (job_abs_deadline (jobs_ex j))))
    cert_base_jobs_ex

check_prefix_backlog_free_at_releases_ex :: EDFPrefixCertEx -> Bool
check_prefix_backlog_free_at_releases_ex p =
  forallb (\j ->
    forallb (\y ->
      case ltb (job_release (jobs_ex y)) (job_release (jobs_ex j)) of {
       True ->
        certified_completed_by_ex (cert_slots_ex p) y
          (job_release (jobs_ex j));
       False -> True}) cert_base_jobs_ex)
    cert_base_jobs_ex

check_periodic_lasso_ex :: EDFInfiniteCertEx -> Bool
check_periodic_lasso_ex c =
  andb
    (andb
      (eqb (cert_period_ex c) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))
      (eqb (cert_task0_shift_ex c) (S (S (S (S (S (S (S O)))))))))
    (eqb (cert_task1_shift_ex c) (S (S (S (S (S O))))))

check_edf_infinite_cert_ex :: EDFInfiniteCertEx -> Bool
check_edf_infinite_cert_ex c =
  andb
    (andb
      (andb
        (andb
          (andb (check_prefix_shape_ex (cert_prefix_ex c))
            (check_prefix_slots_match_ex (cert_prefix_ex c)))
          (check_prefix_edf_ex (cert_prefix_ex c)))
        (check_prefix_service_ex (cert_prefix_ex c)))
      (check_prefix_backlog_free_at_releases_ex (cert_prefix_ex c)))
    (check_periodic_lasso_ex c)

