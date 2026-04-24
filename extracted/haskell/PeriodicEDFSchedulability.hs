module PeriodicEDFSchedulability where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

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

periodic_dbf :: (TaskId -> Task) -> TaskId -> Time -> Nat
periodic_dbf tasks _UU03c4_ h =
  case ltb h (task_relative_deadline (tasks _UU03c4_)) of {
   True -> O;
   False ->
    mul (S
      (div (sub h (task_relative_deadline (tasks _UU03c4_)))
        (task_period (tasks _UU03c4_))))
      (task_cost (tasks _UU03c4_))}

taskset_periodic_dbf :: (TaskId -> Task) -> (List TaskId) -> Time -> Nat
taskset_periodic_dbf tasks enumT h =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    add (periodic_dbf tasks _UU03c4_ h) (taskset_periodic_dbf tasks enumT' h)}

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

task_release_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                            Time -> List Time
task_release_points_upto tasks offset _UU03c4_ h =
  filter (\t -> leb t h)
    (map (expected_release tasks offset _UU03c4_) (bounded_time_points h))

task_deadline_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                             -> Time -> List Time
task_deadline_points_upto tasks offset _UU03c4_ h =
  filter (\t -> leb t h)
    (map (expected_abs_deadline tasks offset _UU03c4_)
      (bounded_time_points h))

critical_dbf_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                            TaskId) -> Time -> List Time
critical_dbf_points_upto tasks offset enumT h =
  Cons O (Cons h
    (app (bounded_time_points h)
      (app
        (flat_map (\_UU03c4_ ->
          task_release_points_upto tasks offset _UU03c4_ h) enumT)
        (flat_map (\_UU03c4_ ->
          task_deadline_points_upto tasks offset _UU03c4_ h) enumT))))

dbf_test_upto :: (TaskId -> Task) -> (List TaskId) -> Time -> Bool
dbf_test_upto tasks enumT h =
  forallb (\t -> leb (taskset_periodic_dbf tasks enumT t) t)
    (critical_dbf_points_upto tasks (\_ -> O) enumT h)

first_dbf_overload_upto :: (TaskId -> Task) -> (List TaskId) -> Time ->
                           Option Time
first_dbf_overload_upto tasks enumT h =
  find (\t -> negb (leb (taskset_periodic_dbf tasks enumT t) t))
    (critical_dbf_points_upto tasks (\_ -> O) enumT h)

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

scalar_dbf_cutoff_bound :: (TaskId -> Task) -> (List TaskId) -> Time
scalar_dbf_cutoff_bound tasks enumT =
  add (periodic_max_relative_deadline tasks enumT)
    (mul (S (periodic_max_relative_deadline tasks enumT))
      (periodic_hyperperiod tasks enumT))

dbf_test_by_cutoff :: (TaskId -> Task) -> (List TaskId) -> Bool
dbf_test_by_cutoff tasks enumT =
  dbf_test_upto tasks enumT (scalar_dbf_cutoff_bound tasks enumT)

data ExtractedPeriodicTask =
   MkExtractedPeriodicTask Nat Nat Nat

extracted_task_cost :: ExtractedPeriodicTask -> Nat
extracted_task_cost e =
  case e of {
   MkExtractedPeriodicTask extracted_task_cost0 _ _ -> extracted_task_cost0}

extracted_task_period :: ExtractedPeriodicTask -> Nat
extracted_task_period e =
  case e of {
   MkExtractedPeriodicTask _ extracted_task_period0 _ ->
    extracted_task_period0}

extracted_task_relative_deadline :: ExtractedPeriodicTask -> Nat
extracted_task_relative_deadline e =
  case e of {
   MkExtractedPeriodicTask _ _ extracted_task_relative_deadline0 ->
    extracted_task_relative_deadline0}

task_of_extracted :: ExtractedPeriodicTask -> Task
task_of_extracted _UU03c4_ =
  MkTask (extracted_task_cost _UU03c4_) (extracted_task_period _UU03c4_)
    (extracted_task_relative_deadline _UU03c4_)

default_extracted_periodic_task :: ExtractedPeriodicTask
default_extracted_periodic_task =
  MkExtractedPeriodicTask (S O) (S O) (S O)

tasks_of_extracted_list :: (List ExtractedPeriodicTask) -> TaskId -> Task
tasks_of_extracted_list ts _UU03c4_ =
  task_of_extracted (nth _UU03c4_ ts default_extracted_periodic_task)

enumT_of_extracted_list :: (List ExtractedPeriodicTask) -> List TaskId
enumT_of_extracted_list ts =
  seq O (length ts)

extracted_task_wf :: ExtractedPeriodicTask -> Bool
extracted_task_wf _UU03c4_ =
  andb
    (andb (ltb O (extracted_task_cost _UU03c4_))
      (ltb O (extracted_task_period _UU03c4_)))
    (ltb O (extracted_task_relative_deadline _UU03c4_))

extracted_taskset_wf :: (List ExtractedPeriodicTask) -> Bool
extracted_taskset_wf ts =
  forallb extracted_task_wf ts

extracted_taskset_dbf_test :: (List ExtractedPeriodicTask) -> Bool
extracted_taskset_dbf_test ts =
  dbf_test_by_cutoff (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts)

edf_schedulability_decide :: (List ExtractedPeriodicTask) -> Bool
edf_schedulability_decide ts =
  andb (extracted_taskset_wf ts) (extracted_taskset_dbf_test ts)

edf_schedulability_counterexample :: (List ExtractedPeriodicTask) -> Option
                                     Time
edf_schedulability_counterexample ts =
  first_dbf_overload_upto (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts)
    (scalar_dbf_cutoff_bound (tasks_of_extracted_list ts)
      (enumT_of_extracted_list ts))

