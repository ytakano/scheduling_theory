module JitteredPeriodicEDFSchedulability where

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

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

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

add0 :: Nat -> Nat -> Nat
add0 n m =
  case n of {
   O -> m;
   S p -> S (add0 p m)}

mul0 :: Nat -> Nat -> Nat
mul0 n m =
  case n of {
   O -> O;
   S p -> add0 m (mul0 p m)}

sub0 :: Nat -> Nat -> Nat
sub0 n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub0 k l}}

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

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' -> case m of {
            O -> n;
            S m' -> S (max n' m')}}

min :: Nat -> Nat -> Nat
min n m =
  case n of {
   O -> O;
   S n' -> case m of {
            O -> O;
            S m' -> S (min n' m')}}

divmod :: Nat -> Nat -> Nat -> Nat -> Prod Nat Nat
divmod x y q u =
  case x of {
   O -> Pair q u;
   S x' -> case u of {
            O -> divmod x' y (S q) y;
            S u' -> divmod x' y q u'}}

div :: Nat -> Nat -> Nat
div x y =
  case y of {
   O -> y;
   S y' -> fst (divmod x y' O y')}

modulo :: Nat -> Nat -> Nat
modulo x y =
  case y of {
   O -> x;
   S y' -> sub0 y' (snd (divmod x y' O y'))}

gcd :: Nat -> Nat -> Nat
gcd a b =
  case a of {
   O -> b;
   S a' -> gcd (modulo b (S a')) (S a')}

lcm :: Nat -> Nat -> Nat
lcm a b =
  mul0 a (div b (gcd a b))

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a l0 -> Cons (f a) (map f l0)}

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

flat_map :: (a1 -> List a2) -> (List a1) -> List a2
flat_map f l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app (f x) (flat_map f l0)}

forallb :: (a1 -> Bool) -> (List a1) -> Bool
forallb f l =
  case l of {
   Nil -> True;
   Cons a l0 -> andb (f a) (forallb f l0)}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

find :: (a1 -> Bool) -> (List a1) -> Option a1
find f l =
  case l of {
   Nil -> None;
   Cons x tl -> case f x of {
                 True -> Some x;
                 False -> find f tl}}

type TaskId = Nat

type Time = Nat

data Task =
   MkTask Nat Nat Nat

task_cost :: Task -> Nat
task_cost t =
  case t of {
   MkTask task_cost0 _ _ -> task_cost0}

task_period :: Task -> Nat
task_period t =
  case t of {
   MkTask _ task_period0 _ -> task_period0}

task_relative_deadline :: Task -> Nat
task_relative_deadline t =
  case t of {
   MkTask _ _ task_relative_deadline0 -> task_relative_deadline0}

expected_release :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId -> Nat ->
                    Time
expected_release tasks offset _UU03c4_ k =
  add (offset _UU03c4_) (mul k (task_period (tasks _UU03c4_)))

expected_abs_deadline :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                         Nat -> Time
expected_abs_deadline tasks offset _UU03c4_ k =
  add (expected_release tasks offset _UU03c4_ k)
    (task_relative_deadline (tasks _UU03c4_))

bounded_time_points :: Time -> List Time
bounded_time_points h =
  seq O (S h)

task_deadline_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                             -> Time -> List Time
task_deadline_points_upto tasks offset _UU03c4_ h =
  filter (\t -> leb t h)
    (map (expected_abs_deadline tasks offset _UU03c4_)
      (bounded_time_points h))

critical_dbf_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                            TaskId) -> Time -> List Time
critical_dbf_points_upto tasks offset enumT h =
  app (bounded_time_points h)
    (flat_map (\_UU03c4_ ->
      task_deadline_points_upto tasks offset _UU03c4_ h) enumT)

critical_dbf_windows_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                             TaskId) -> Time -> List (Prod Time Time)
critical_dbf_windows_upto tasks offset enumT h =
  let {points = critical_dbf_points_upto tasks offset enumT h} in
  flat_map (\t1 ->
    map (\t2 -> Pair t1 t2)
      (filter (\t2 -> andb (leb t1 t2) (leb t2 h)) points))
    points

periodic_hyperperiod :: (TaskId -> Task) -> (List TaskId) -> Time
periodic_hyperperiod tasks enumT =
  case enumT of {
   Nil -> S O;
   Cons _UU03c4_ enumT' ->
    lcm (task_period (tasks _UU03c4_)) (periodic_hyperperiod tasks enumT')}

periodic_max_relative_deadline :: (TaskId -> Task) -> (List TaskId) -> Time
periodic_max_relative_deadline tasks enumT =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    max (task_relative_deadline (tasks _UU03c4_))
      (periodic_max_relative_deadline tasks enumT')}

jittered_index_may_be_in_window_b :: (TaskId -> Task) -> (TaskId -> Time) ->
                                     (TaskId -> Time) -> TaskId -> Time ->
                                     Time -> Nat -> Bool
jittered_index_may_be_in_window_b tasks offset jitter _UU03c4_ t1 t2 k =
  andb (leb (task_relative_deadline (tasks _UU03c4_)) t2)
    (leb (max t1 (expected_release tasks offset _UU03c4_ k))
      (min (sub t2 (task_relative_deadline (tasks _UU03c4_)))
        (add (expected_release tasks offset _UU03c4_ k) (jitter _UU03c4_))))

jittered_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (TaskId -> Time) -> TaskId -> Time -> Time ->
                                Nat
jittered_periodic_dbf_window tasks offset jitter _UU03c4_ t1 t2 =
  mul
    (length
      (filter
        (jittered_index_may_be_in_window_b tasks offset jitter _UU03c4_ t1
          t2)
        (seq O (S t2))))
    (task_cost (tasks _UU03c4_))

taskset_jittered_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> (List 
                                        TaskId) -> Time -> Time -> Nat
taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    add (jittered_periodic_dbf_window tasks offset jitter _UU03c4_ t1 t2)
      (taskset_jittered_periodic_dbf_window tasks offset jitter enumT' t1 t2)}

nat_interval_count :: Nat -> Nat -> Nat
nat_interval_count lo hi =
  case leb lo hi of {
   True -> S (sub hi lo);
   False -> O}

ceil_div_pos :: Nat -> Nat -> Nat
ceil_div_pos n p =
  div (sub (add n p) (S O)) p

ap_first_index_at_or_after :: Nat -> Nat -> Nat -> Nat
ap_first_index_at_or_after start period lo =
  case leb lo start of {
   True -> O;
   False -> ceil_div_pos (sub lo start) period}

ap_index_count :: Nat -> Nat -> Nat -> Nat -> Nat -> Nat
ap_index_count start period lo hi limit =
  case eqb period O of {
   True ->
    case andb (leb lo start) (leb start hi) of {
     True -> S limit;
     False -> O};
   False ->
    case leb start hi of {
     True ->
      let {first = ap_first_index_at_or_after start period lo} in
      let {last = min limit (div (sub hi start) period)} in
      nat_interval_count first last;
     False -> O}}

jittered_periodic_fast_release_count :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> TaskId -> Time
                                        -> Time -> Nat
jittered_periodic_fast_release_count tasks offset jitter _UU03c4_ t1 t2 =
  let {d = task_relative_deadline (tasks _UU03c4_)} in
  case andb (leb d t2) (leb t1 (sub t2 d)) of {
   True ->
    ap_index_count (offset _UU03c4_) (task_period (tasks _UU03c4_))
      (sub t1 (jitter _UU03c4_)) (sub t2 d) t2;
   False -> O}

jittered_periodic_fast_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) ->
                                     (TaskId -> Time) -> TaskId -> Time ->
                                     Time -> Nat
jittered_periodic_fast_dbf_window tasks offset jitter _UU03c4_ t1 t2 =
  mul
    (jittered_periodic_fast_release_count tasks offset jitter _UU03c4_ t1 t2)
    (task_cost (tasks _UU03c4_))

taskset_jittered_periodic_fast_dbf_window :: (TaskId -> Task) -> (TaskId ->
                                             Time) -> (TaskId -> Time) ->
                                             (List TaskId) -> Time -> Time ->
                                             Nat
taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT t1 t2 =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    add
      (jittered_periodic_fast_dbf_window tasks offset jitter _UU03c4_ t1 t2)
      (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT'
        t1 t2)}

type JitteredCompactDbfBasis = List (Prod Time (List Time))

jittered_compact_basis_windows :: JitteredCompactDbfBasis -> List
                                  (Prod Time Time)
jittered_compact_basis_windows basis =
  flat_map (\row ->
    case row of {
     Pair t2 left_edges -> map (\t1 -> Pair t1 t2) left_edges}) basis

jittered_fast_compact_basis_dbf_test :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> (List
                                        TaskId) -> JitteredCompactDbfBasis ->
                                        Bool
jittered_fast_compact_basis_dbf_test tasks offset jitter enumT basis =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      andb (leb t1 t2)
        (leb
          (taskset_jittered_periodic_fast_dbf_window tasks offset jitter
            enumT t1 t2)
          (sub t2 t1))})
    (jittered_compact_basis_windows basis)

jittered_reduced_left_edge_b :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (TaskId -> Time) -> (List TaskId) -> Time ->
                                Time -> Bool
jittered_reduced_left_edge_b tasks offset jitter enumT t2 t1 =
  orb (eqb t1 t2)
    (negb
      (eqb
        (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT
          t1 t2)
        (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT
          (S t1) t2)))

jittered_reduced_left_edges_for_t2 :: (TaskId -> Task) -> (TaskId -> Time) ->
                                      (TaskId -> Time) -> (List TaskId) ->
                                      Time -> List Time
jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2 =
  filter (jittered_reduced_left_edge_b tasks offset jitter enumT t2)
    (bounded_time_points t2)

jittered_reduced_compact_basis_upto :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (TaskId -> Time) -> (List TaskId)
                                       -> Time -> JitteredCompactDbfBasis
jittered_reduced_compact_basis_upto tasks offset jitter enumT h =
  map (\t2 -> Pair t2
    (jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2))
    (bounded_time_points h)

data JitteredEDFDbfCertificate =
   Build_JitteredEDFDbfCertificate Time (List (Prod Time Time)) Bool

jedf_cutoff :: JitteredEDFDbfCertificate -> Time
jedf_cutoff j =
  case j of {
   Build_JitteredEDFDbfCertificate jedf_cutoff0 _ _ -> jedf_cutoff0}

jedf_checked_windows :: JitteredEDFDbfCertificate -> List (Prod Time Time)
jedf_checked_windows j =
  case j of {
   Build_JitteredEDFDbfCertificate _ jedf_checked_windows0 _ ->
    jedf_checked_windows0}

jedf_all_windows_checked :: JitteredEDFDbfCertificate -> Bool
jedf_all_windows_checked j =
  case j of {
   Build_JitteredEDFDbfCertificate _ _ jedf_all_windows_checked0 ->
    jedf_all_windows_checked0}

data JitteredEDFCompactDbfCertificate =
   Build_JitteredEDFCompactDbfCertificate Time JitteredCompactDbfBasis
 Bool

jedf_compact_cutoff :: JitteredEDFCompactDbfCertificate -> Time
jedf_compact_cutoff j =
  case j of {
   Build_JitteredEDFCompactDbfCertificate jedf_compact_cutoff0 _ _ ->
    jedf_compact_cutoff0}

jedf_compact_basis :: JitteredEDFCompactDbfCertificate ->
                      JitteredCompactDbfBasis
jedf_compact_basis j =
  case j of {
   Build_JitteredEDFCompactDbfCertificate _ jedf_compact_basis0 _ ->
    jedf_compact_basis0}

jedf_all_basis_checked :: JitteredEDFCompactDbfCertificate -> Bool
jedf_all_basis_checked j =
  case j of {
   Build_JitteredEDFCompactDbfCertificate _ _ jedf_all_basis_checked0 ->
    jedf_all_basis_checked0}

time_pair_eqb :: (Prod Time Time) -> (Prod Time Time) -> Bool
time_pair_eqb w1 w2 =
  case w1 of {
   Pair a1 b1 -> case w2 of {
                  Pair a2 b2 -> andb (eqb a1 a2) (eqb b1 b2)}}

time_pair_list_eqb :: (List (Prod Time Time)) -> (List (Prod Time Time)) ->
                      Bool
time_pair_list_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> True;
           Cons _ _ -> False};
   Cons x xs' ->
    case ys of {
     Nil -> False;
     Cons y ys' -> andb (time_pair_eqb x y) (time_pair_list_eqb xs' ys')}}

time_list_eqb :: (List Time) -> (List Time) -> Bool
time_list_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> True;
           Cons _ _ -> False};
   Cons x xs' ->
    case ys of {
     Nil -> False;
     Cons y ys' -> andb (eqb x y) (time_list_eqb xs' ys')}}

compact_dbf_basis_row_eqb :: (Prod Time (List Time)) -> (Prod Time
                             (List Time)) -> Bool
compact_dbf_basis_row_eqb r1 r2 =
  case r1 of {
   Pair t2_1 left_edges1 ->
    case r2 of {
     Pair t2_2 left_edges2 ->
      andb (eqb t2_1 t2_2) (time_list_eqb left_edges1 left_edges2)}}

compact_dbf_basis_eqb :: JitteredCompactDbfBasis -> JitteredCompactDbfBasis
                         -> Bool
compact_dbf_basis_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> True;
           Cons _ _ -> False};
   Cons x xs' ->
    case ys of {
     Nil -> False;
     Cons y ys' ->
      andb (compact_dbf_basis_row_eqb x y) (compact_dbf_basis_eqb xs' ys')}}

check_jittered_edf_dbf_certificate_fields :: Time -> (List (Prod Time Time))
                                             -> JitteredEDFDbfCertificate ->
                                             Bool
check_jittered_edf_dbf_certificate_fields expected_cutoff expected_windows cert =
  andb
    (andb (eqb (jedf_cutoff cert) expected_cutoff)
      (time_pair_list_eqb (jedf_checked_windows cert) expected_windows))
    (jedf_all_windows_checked cert)

check_jittered_edf_compact_dbf_certificate_fields :: Time ->
                                                     JitteredCompactDbfBasis
                                                     ->
                                                     JitteredEDFCompactDbfCertificate
                                                     -> Bool
check_jittered_edf_compact_dbf_certificate_fields expected_cutoff expected_basis cert =
  andb
    (andb (eqb (jedf_compact_cutoff cert) expected_cutoff)
      (compact_dbf_basis_eqb (jedf_compact_basis cert) expected_basis))
    (jedf_all_basis_checked cert)

jittered_window_dbf_test_upto :: (TaskId -> Task) -> (TaskId -> Time) ->
                                 (TaskId -> Time) -> (List TaskId) -> Time ->
                                 Bool
jittered_window_dbf_test_upto tasks offset jitter enumT h =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      leb
        (taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1
          t2)
        (sub t2 t1)})
    (critical_dbf_windows_upto tasks offset enumT h)

first_jittered_window_dbf_overload_upto :: (TaskId -> Task) -> (TaskId ->
                                           Time) -> (TaskId -> Time) -> (List
                                           TaskId) -> Time -> Option
                                           (Prod Time Time)
first_jittered_window_dbf_overload_upto tasks offset jitter enumT h =
  find (\w ->
    case w of {
     Pair t1 t2 ->
      negb
        (leb
          (taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1
            t2)
          (sub t2 t1))})
    (critical_dbf_windows_upto tasks offset enumT h)

data ExtractedPeriodicTask =
   MkExtractedPeriodicTask Nat Nat Nat Nat

extracted_task_cost :: ExtractedPeriodicTask -> Nat
extracted_task_cost e =
  case e of {
   MkExtractedPeriodicTask extracted_task_cost0 _ _ _ -> extracted_task_cost0}

extracted_task_period :: ExtractedPeriodicTask -> Nat
extracted_task_period e =
  case e of {
   MkExtractedPeriodicTask _ extracted_task_period0 _ _ ->
    extracted_task_period0}

extracted_task_relative_deadline :: ExtractedPeriodicTask -> Nat
extracted_task_relative_deadline e =
  case e of {
   MkExtractedPeriodicTask _ _ extracted_task_relative_deadline0 _ ->
    extracted_task_relative_deadline0}

extracted_task_offset :: ExtractedPeriodicTask -> Nat
extracted_task_offset e =
  case e of {
   MkExtractedPeriodicTask _ _ _ extracted_task_offset0 ->
    extracted_task_offset0}

data ExtractedJitteredPeriodicTask =
   MkExtractedJitteredPeriodicTask Nat Nat Nat Nat Nat

ejp_cost :: ExtractedJitteredPeriodicTask -> Nat
ejp_cost e =
  case e of {
   MkExtractedJitteredPeriodicTask ejp_cost0 _ _ _ _ -> ejp_cost0}

ejp_period :: ExtractedJitteredPeriodicTask -> Nat
ejp_period e =
  case e of {
   MkExtractedJitteredPeriodicTask _ ejp_period0 _ _ _ -> ejp_period0}

ejp_relative_deadline :: ExtractedJitteredPeriodicTask -> Nat
ejp_relative_deadline e =
  case e of {
   MkExtractedJitteredPeriodicTask _ _ ejp_relative_deadline0 _ _ ->
    ejp_relative_deadline0}

ejp_offset :: ExtractedJitteredPeriodicTask -> Nat
ejp_offset e =
  case e of {
   MkExtractedJitteredPeriodicTask _ _ _ ejp_offset0 _ -> ejp_offset0}

ejp_release_jitter :: ExtractedJitteredPeriodicTask -> Nat
ejp_release_jitter e =
  case e of {
   MkExtractedJitteredPeriodicTask _ _ _ _ ejp_release_jitter0 ->
    ejp_release_jitter0}

task_of_extracted_jittered :: ExtractedJitteredPeriodicTask -> Task
task_of_extracted_jittered _UU03c4_ =
  MkTask (ejp_cost _UU03c4_) (ejp_period _UU03c4_)
    (ejp_relative_deadline _UU03c4_)

default_extracted_jittered_periodic_task :: ExtractedJitteredPeriodicTask
default_extracted_jittered_periodic_task =
  MkExtractedJitteredPeriodicTask (S O) (S O) (S O) O O

extracted_periodic_as_jittered_zero_jitter :: ExtractedPeriodicTask ->
                                              ExtractedJitteredPeriodicTask
extracted_periodic_as_jittered_zero_jitter _UU03c4_ =
  MkExtractedJitteredPeriodicTask (extracted_task_cost _UU03c4_)
    (extracted_task_period _UU03c4_)
    (extracted_task_relative_deadline _UU03c4_)
    (extracted_task_offset _UU03c4_) O

jittered_tasks_of_extracted_list :: (List ExtractedJitteredPeriodicTask) ->
                                    TaskId -> Task
jittered_tasks_of_extracted_list ts _UU03c4_ =
  task_of_extracted_jittered
    (nth _UU03c4_ ts default_extracted_jittered_periodic_task)

jittered_offset_of_extracted_list :: (List ExtractedJitteredPeriodicTask) ->
                                     TaskId -> Time
jittered_offset_of_extracted_list ts _UU03c4_ =
  ejp_offset (nth _UU03c4_ ts default_extracted_jittered_periodic_task)

jitter_of_extracted_list :: (List ExtractedJitteredPeriodicTask) -> TaskId ->
                            Time
jitter_of_extracted_list ts _UU03c4_ =
  ejp_release_jitter
    (nth _UU03c4_ ts default_extracted_jittered_periodic_task)

jittered_enumT_of_extracted_list :: (List ExtractedJitteredPeriodicTask) ->
                                    List TaskId
jittered_enumT_of_extracted_list ts =
  seq O (length ts)

extracted_jittered_task_wf :: ExtractedJitteredPeriodicTask -> Bool
extracted_jittered_task_wf _UU03c4_ =
  andb (andb (ltb O (ejp_cost _UU03c4_)) (ltb O (ejp_period _UU03c4_)))
    (ltb O (ejp_relative_deadline _UU03c4_))

extracted_jittered_taskset_wf :: (List ExtractedJitteredPeriodicTask) -> Bool
extracted_jittered_taskset_wf ts =
  forallb extracted_jittered_task_wf ts

periodic_max_offset :: (TaskId -> Time) -> (List TaskId) -> Time
periodic_max_offset offset enumT =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    max (offset _UU03c4_) (periodic_max_offset offset enumT')}

offset_window_dbf_cutoff_bound :: (TaskId -> Task) -> (TaskId -> Time) ->
                                  (List TaskId) -> Time
offset_window_dbf_cutoff_bound tasks offset enumT =
  let {
   horizon_base = add
                    (add (periodic_max_offset offset enumT)
                      (periodic_max_relative_deadline tasks enumT))
                    (periodic_hyperperiod tasks enumT)}
  in
  add horizon_base (mul (S horizon_base) (periodic_hyperperiod tasks enumT))

jittered_max_release_jitter :: (TaskId -> Time) -> (List TaskId) -> Time
jittered_max_release_jitter jitter enumT =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    max (jitter _UU03c4_) (jittered_max_release_jitter jitter enumT')}

jittered_offset_window_dbf_cutoff_bound :: (TaskId -> Task) -> (TaskId ->
                                           Time) -> (TaskId -> Time) -> (List
                                           TaskId) -> Time
jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT =
  add (offset_window_dbf_cutoff_bound tasks offset enumT)
    (jittered_max_release_jitter jitter enumT)

jittered_offset_window_dbf_test_by_cutoff :: (TaskId -> Task) -> (TaskId ->
                                             Time) -> (TaskId -> Time) ->
                                             (List TaskId) -> Bool
jittered_offset_window_dbf_test_by_cutoff tasks offset jitter enumT =
  jittered_window_dbf_test_upto tasks offset jitter enumT
    (jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT)

extracted_jittered_offset_window_dbf_cutoff_bound :: (List
                                                     ExtractedJitteredPeriodicTask)
                                                     -> Time
extracted_jittered_offset_window_dbf_cutoff_bound ts =
  jittered_offset_window_dbf_cutoff_bound
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)

extracted_jittered_offset_window_dbf_test_by_cutoff :: (List
                                                       ExtractedJitteredPeriodicTask)
                                                       -> Bool
extracted_jittered_offset_window_dbf_test_by_cutoff ts =
  jittered_offset_window_dbf_test_by_cutoff
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)

extracted_jittered_offset_window_dbf_counterexample_by_cutoff :: (List
                                                                 ExtractedJitteredPeriodicTask)
                                                                 -> Option
                                                                 (Prod 
                                                                 Time 
                                                                 Time)
extracted_jittered_offset_window_dbf_counterexample_by_cutoff ts =
  first_jittered_window_dbf_overload_upto
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (extracted_jittered_offset_window_dbf_cutoff_bound ts)

extracted_jittered_offset_window_dbf_decide_by_cutoff :: (List
                                                         ExtractedJitteredPeriodicTask)
                                                         -> Bool
extracted_jittered_offset_window_dbf_decide_by_cutoff ts =
  andb (extracted_jittered_taskset_wf ts)
    (extracted_jittered_offset_window_dbf_test_by_cutoff ts)

jittered_periodic_offset_window_schedulability_cutoff_bound :: (List
                                                               ExtractedJitteredPeriodicTask)
                                                               -> Time
jittered_periodic_offset_window_schedulability_cutoff_bound =
  extracted_jittered_offset_window_dbf_cutoff_bound

jittered_periodic_offset_window_schedulability_decide :: (List
                                                         ExtractedJitteredPeriodicTask)
                                                         -> Bool
jittered_periodic_offset_window_schedulability_decide =
  extracted_jittered_offset_window_dbf_decide_by_cutoff

jittered_periodic_offset_window_schedulability_counterexample :: (List
                                                                 ExtractedJitteredPeriodicTask)
                                                                 -> Option
                                                                 (Prod 
                                                                 Time 
                                                                 Time)
jittered_periodic_offset_window_schedulability_counterexample =
  extracted_jittered_offset_window_dbf_counterexample_by_cutoff

jittered_edf_dbf_certificate_expected_cutoff :: (List
                                                ExtractedJitteredPeriodicTask)
                                                -> Time
jittered_edf_dbf_certificate_expected_cutoff =
  extracted_jittered_offset_window_dbf_cutoff_bound

jittered_edf_dbf_certificate_expected_windows :: (List
                                                 ExtractedJitteredPeriodicTask)
                                                 -> List (Prod Time Time)
jittered_edf_dbf_certificate_expected_windows ts =
  critical_dbf_windows_upto (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (jittered_edf_dbf_certificate_expected_cutoff ts)

jittered_edf_compact_dbf_certificate_expected_cutoff :: (List
                                                        ExtractedJitteredPeriodicTask)
                                                        -> Time
jittered_edf_compact_dbf_certificate_expected_cutoff =
  extracted_jittered_offset_window_dbf_cutoff_bound

jittered_edf_compact_dbf_certificate_expected_basis :: (List
                                                       ExtractedJitteredPeriodicTask)
                                                       ->
                                                       JitteredCompactDbfBasis
jittered_edf_compact_dbf_certificate_expected_basis ts =
  jittered_reduced_compact_basis_upto (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (jittered_edf_compact_dbf_certificate_expected_cutoff ts)

check_jittered_edf_dbf_certificate_extracted :: (List
                                                ExtractedJitteredPeriodicTask)
                                                -> JitteredEDFDbfCertificate
                                                -> Bool
check_jittered_edf_dbf_certificate_extracted ts cert =
  andb
    (andb (extracted_jittered_taskset_wf ts)
      (check_jittered_edf_dbf_certificate_fields
        (jittered_edf_dbf_certificate_expected_cutoff ts)
        (jittered_edf_dbf_certificate_expected_windows ts) cert))
    (extracted_jittered_offset_window_dbf_test_by_cutoff ts)

check_jittered_edf_compact_dbf_certificate_extracted :: (List
                                                        ExtractedJitteredPeriodicTask)
                                                        ->
                                                        JitteredEDFCompactDbfCertificate
                                                        -> Bool
check_jittered_edf_compact_dbf_certificate_extracted ts cert =
  andb
    (andb (extracted_jittered_taskset_wf ts)
      (check_jittered_edf_compact_dbf_certificate_fields
        (jittered_edf_compact_dbf_certificate_expected_cutoff ts)
        (jittered_edf_compact_dbf_certificate_expected_basis ts) cert))
    (jittered_fast_compact_basis_dbf_test
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts) (jedf_compact_basis cert))
