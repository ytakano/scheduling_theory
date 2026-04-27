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

option_map :: (a1 -> a2) -> (Option a1) -> Option a2
option_map f o =
  case o of {
   Some a -> Some (f a);
   None -> None}

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

nth_error :: (List a1) -> Nat -> Option a1
nth_error l n =
  case n of {
   O -> case l of {
         Nil -> None;
         Cons x _ -> Some x};
   S n0 -> case l of {
            Nil -> None;
            Cons _ l' -> nth_error l' n0}}

flat_map :: (a1 -> List a2) -> (List a1) -> List a2
flat_map f l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app (f x) (flat_map f l0)}

existsb :: (a1 -> Bool) -> (List a1) -> Bool
existsb f l =
  case l of {
   Nil -> False;
   Cons a l0 -> orb (f a) (existsb f l0)}

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

combine :: (List a1) -> (List a2) -> List (Prod a1 a2)
combine l l' =
  case l of {
   Nil -> Nil;
   Cons x tl ->
    case l' of {
     Nil -> Nil;
     Cons y tl' -> Cons (Pair x y) (combine tl tl')}}

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

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

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

leb0 :: Z -> Z -> Bool
leb0 x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

of_nat :: Nat -> Z
of_nat n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

type JobId = Nat

type TaskId = Nat

type CPU = Nat

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

job_abs_deadline :: Job -> Time
job_abs_deadline j =
  case j of {
   MkJob _ _ _ _ job_abs_deadline0 _ -> job_abs_deadline0}

job_blocked :: Job -> Time -> Bool
job_blocked j =
  case j of {
   MkJob _ _ _ _ _ job_blocked0 -> job_blocked0}

type Schedule = Time -> CPU -> Option JobId

data EDFPrefixCert job =
   Build_EDFPrefixCert Time (List job) (List (Option job)) (List Time) 
 (List (List Bool))

prefix_horizon :: (EDFPrefixCert a1) -> Time
prefix_horizon e =
  case e of {
   Build_EDFPrefixCert prefix_horizon0 _ _ _ _ -> prefix_horizon0}

prefix_basis_jobs :: (EDFPrefixCert a1) -> List a1
prefix_basis_jobs e =
  case e of {
   Build_EDFPrefixCert _ prefix_basis_jobs0 _ _ _ -> prefix_basis_jobs0}

prefix_slots :: (EDFPrefixCert a1) -> List (Option a1)
prefix_slots e =
  case e of {
   Build_EDFPrefixCert _ _ prefix_slots0 _ _ -> prefix_slots0}

prefix_completed_by :: (EDFPrefixCert a1) -> List Time
prefix_completed_by e =
  case e of {
   Build_EDFPrefixCert _ _ _ prefix_completed_by0 _ -> prefix_completed_by0}

prefix_backlog_free_matrix :: (EDFPrefixCert a1) -> List (List Bool)
prefix_backlog_free_matrix e =
  case e of {
   Build_EDFPrefixCert _ _ _ _ prefix_backlog_free_matrix0 ->
    prefix_backlog_free_matrix0}

data EDFTransportClass job =
   Build_EDFTransportClass job Time Time

transport_rep_job :: (EDFTransportClass a1) -> a1
transport_rep_job e =
  case e of {
   Build_EDFTransportClass transport_rep_job0 _ _ -> transport_rep_job0}

data EDFTransportCert job =
   Build_EDFTransportCert Time (List job) (List (EDFTransportClass job)) 
 (List Nat) (List Nat)

transport_period :: (EDFTransportCert a1) -> Time
transport_period e =
  case e of {
   Build_EDFTransportCert transport_period0 _ _ _ _ -> transport_period0}

transport_basis_jobs :: (EDFTransportCert a1) -> List a1
transport_basis_jobs e =
  case e of {
   Build_EDFTransportCert _ transport_basis_jobs0 _ _ _ ->
    transport_basis_jobs0}

transport_classes :: (EDFTransportCert a1) -> List (EDFTransportClass a1)
transport_classes e =
  case e of {
   Build_EDFTransportCert _ _ transport_classes0 _ _ -> transport_classes0}

transport_job_class :: (EDFTransportCert a1) -> List Nat
transport_job_class e =
  case e of {
   Build_EDFTransportCert _ _ _ transport_job_class0 _ ->
    transport_job_class0}

transport_job_shift :: (EDFTransportCert a1) -> List Nat
transport_job_shift e =
  case e of {
   Build_EDFTransportCert _ _ _ _ transport_job_shift0 ->
    transport_job_shift0}

data EDFDBFCert =
   Build_EDFDBFCert Time (List Bool)

data EDFInfiniteCert job =
   Build_EDFInfiniteCert (EDFPrefixCert job) (EDFTransportCert job) EDFDBFCert

cert_prefix :: (EDFInfiniteCert a1) -> EDFPrefixCert a1
cert_prefix e =
  case e of {
   Build_EDFInfiniteCert cert_prefix0 _ _ -> cert_prefix0}

cert_transport :: (EDFInfiniteCert a1) -> EDFTransportCert a1
cert_transport e =
  case e of {
   Build_EDFInfiniteCert _ cert_transport0 _ -> cert_transport0}

check_bool_rows_have_length :: Nat -> (List (List Bool)) -> Bool
check_bool_rows_have_length n rows =
  forallb (\row -> eqb (length row) n) rows

check_nat_entries_below :: Nat -> (List Nat) -> Bool
check_nat_entries_below bound xs =
  forallb (\x -> ltb x bound) xs

check_prefix_cert :: (EDFPrefixCert a1) -> Bool
check_prefix_cert c =
  andb
    (andb
      (andb (eqb (length (prefix_slots c)) (prefix_horizon c))
        (eqb (length (prefix_completed_by c)) (length (prefix_basis_jobs c))))
      (eqb (length (prefix_backlog_free_matrix c))
        (length (prefix_basis_jobs c))))
    (check_bool_rows_have_length (length (prefix_basis_jobs c))
      (prefix_backlog_free_matrix c))

check_transport_cert :: (EDFTransportCert a1) -> Bool
check_transport_cert c =
  andb
    (andb
      (andb (ltb O (transport_period c))
        (eqb (length (transport_job_class c))
          (length (transport_basis_jobs c))))
      (eqb (length (transport_job_shift c))
        (length (transport_basis_jobs c))))
    (check_nat_entries_below (length (transport_classes c))
      (transport_job_class c))

runs_on :: Schedule -> JobId -> Time -> CPU -> Bool
runs_on sched j t c =
  case sched t c of {
   Some j' -> eqb j' j;
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

type GenericSchedulingAlgorithm =
  (JobId -> Job) -> Nat -> Schedule -> Time -> (List JobId) -> Option JobId
  -- singleton inductive, whose constructor was mkGenericSchedulingAlgorithm
  
choose :: GenericSchedulingAlgorithm -> (JobId -> Job) -> Nat -> Schedule ->
          Time -> (List JobId) -> Option JobId
choose g =
  g

type CandidateSource =
  (JobId -> Job) -> Nat -> Schedule -> Time -> List JobId

enum_candidates_of :: (List JobId) -> CandidateSource
enum_candidates_of enumJ _ _ _ _ =
  enumJ

expected_release :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId -> Nat ->
                    Time
expected_release tasks offset _UU03c4_ k =
  add (offset _UU03c4_) (mul k (task_period (tasks _UU03c4_)))

expected_abs_deadline :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                         Nat -> Time
expected_abs_deadline tasks offset _UU03c4_ k =
  add (expected_release tasks offset _UU03c4_ k)
    (task_relative_deadline (tasks _UU03c4_))

generated_periodic_job :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                          Nat -> Job
generated_periodic_job tasks offset _UU03c4_ k =
  MkJob _UU03c4_ k (expected_release tasks offset _UU03c4_ k)
    (task_cost (tasks _UU03c4_))
    (expected_abs_deadline tasks offset _UU03c4_ k) (\_ -> False)

type PeriodicCodec =
  TaskId -> Nat -> JobId
  -- singleton inductive, whose constructor was mkPeriodicCodec
  
global_periodic_job_id_of :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId
                             -> Job) -> PeriodicCodec -> TaskId -> Nat ->
                             JobId
global_periodic_job_id_of _ _ _ p =
  p

task_position_in_enumT :: (List TaskId) -> TaskId -> Nat
task_position_in_enumT enumT _UU03c4_ =
  case enumT of {
   Nil -> O;
   Cons x xs ->
    case eqb x _UU03c4_ of {
     True -> O;
     False -> S (task_position_in_enumT xs _UU03c4_)}}

encode_job_id_from_enumT :: (List TaskId) -> TaskId -> Nat -> JobId
encode_job_id_from_enumT enumT _UU03c4_ k =
  add (task_position_in_enumT enumT _UU03c4_) (mul (length enumT) k)

decode_job_id_from_enumT :: (List TaskId) -> JobId -> Prod Nat Nat
decode_job_id_from_enumT enumT j =
  case length enumT of {
   O -> Pair O j;
   S n0 -> let {n = S n0} in Pair (modulo j n) (div j n)}

canonical_periodic_jobs_from_enumT :: (TaskId -> Task) -> (TaskId -> Time) ->
                                      (List TaskId) -> JobId -> Job
canonical_periodic_jobs_from_enumT tasks offset enumT j =
  case decode_job_id_from_enumT enumT j of {
   Pair pos k ->
    case nth_error enumT pos of {
     Some _UU03c4_ -> generated_periodic_job tasks offset _UU03c4_ k;
     None -> MkJob O j O (S (task_cost (tasks O))) O (\_ -> False)}}

periodic_codec_of_enumT :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                           TaskId) -> PeriodicCodec
periodic_codec_of_enumT _ _ =
  encode_job_id_from_enumT

zero_offset_periodic_codec_of_tasks :: (TaskId -> Task) -> (List TaskId) ->
                                       PeriodicCodec
zero_offset_periodic_codec_of_tasks tasks enumT =
  periodic_codec_of_enumT tasks (\_ -> O) enumT

type PeriodicFiniteHorizonCodec =
  TaskId -> Nat -> JobId
  -- singleton inductive, whose constructor was mkPeriodicFiniteHorizonCodec
  
periodic_job_id_of :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId -> Job)
                      -> Time -> PeriodicFiniteHorizonCodec -> TaskId -> Nat
                      -> JobId
periodic_job_id_of _ _ _ _ p =
  p

periodic_finite_horizon_codec_of :: (TaskId -> Task) -> (TaskId -> Time) ->
                                    (JobId -> Job) -> Time -> PeriodicCodec
                                    -> PeriodicFiniteHorizonCodec
periodic_finite_horizon_codec_of tasks offset jobs _ codec =
  global_periodic_job_id_of tasks offset jobs codec

enum_periodic_indices_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                              -> Time -> List Nat
enum_periodic_indices_upto tasks offset _UU03c4_ h =
  filter (\k -> ltb (expected_release tasks offset _UU03c4_ k) h) (seq O h)

enum_periodic_jobs_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId ->
                           Job) -> Time -> (List TaskId) ->
                           PeriodicFiniteHorizonCodec -> List JobId
enum_periodic_jobs_upto tasks offset jobs h enumT codec =
  let {id_of = periodic_job_id_of tasks offset jobs h codec} in
  flat_map (\_UU03c4_ ->
    map (id_of _UU03c4_) (enum_periodic_indices_upto tasks offset _UU03c4_ h))
    enumT

enum_periodic_jobs_before :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId
                             -> Job) -> (List TaskId) -> PeriodicCodec ->
                             Time -> List JobId
enum_periodic_jobs_before tasks offset jobs enumT codec t =
  enum_periodic_jobs_upto tasks offset jobs t enumT
    (periodic_finite_horizon_codec_of tasks offset jobs t codec)

periodic_index_in_window :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                            Time -> Time -> Nat -> Bool
periodic_index_in_window tasks offset _UU03c4_ t1 t2 k =
  andb (leb t1 (expected_release tasks offset _UU03c4_ k))
    (leb (expected_abs_deadline tasks offset _UU03c4_ k) t2)

periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId -> Time
                       -> Time -> Nat
periodic_dbf_window tasks offset _UU03c4_ t1 t2 =
  mul
    (length
      (filter (periodic_index_in_window tasks offset _UU03c4_ t1 t2)
        (seq O (S t2))))
    (task_cost (tasks _UU03c4_))

taskset_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                               TaskId) -> Time -> Time -> Nat
taskset_periodic_dbf_window tasks offset enumT t1 t2 =
  case enumT of {
   Nil -> O;
   Cons _UU03c4_ enumT' ->
    add (periodic_dbf_window tasks offset _UU03c4_ t1 t2)
      (taskset_periodic_dbf_window tasks offset enumT' t1 t2)}

generated_schedule_prefix :: GenericSchedulingAlgorithm -> CandidateSource ->
                             (JobId -> Job) -> Time -> Schedule
generated_schedule_prefix alg candidates_of jobs h =
  case h of {
   O -> (\_ _ -> None);
   S h' ->
    let {pref = generated_schedule_prefix alg candidates_of jobs h'} in
    (\t c ->
    case ltb t h' of {
     True -> pref t c;
     False ->
      case eqb t h' of {
       True ->
        case eqb c O of {
         True ->
          choose alg jobs (S O) pref h' (candidates_of jobs (S O) pref h');
         False -> None};
       False -> None}})}

generated_schedule :: GenericSchedulingAlgorithm -> CandidateSource -> (JobId
                      -> Job) -> Schedule
generated_schedule alg candidates_of jobs t c =
  generated_schedule_prefix alg candidates_of jobs (S t) t c

min_metric_job :: (JobId -> Z) -> (List JobId) -> Option JobId
min_metric_job metric l =
  case l of {
   Nil -> None;
   Cons j rest ->
    case min_metric_job metric rest of {
     Some j' ->
      case leb0 (metric j) (metric j') of {
       True -> Some j;
       False -> Some j'};
     None -> Some j}}

choose_min_metric :: (JobId -> Z) -> (JobId -> Job) -> Nat -> Schedule ->
                     Time -> (List JobId) -> Option JobId
choose_min_metric metric jobs m sched t candidates =
  min_metric_job metric
    (filter (\j -> eligibleb jobs m sched j t) candidates)

edf_metric :: (JobId -> Job) -> JobId -> Z
edf_metric jobs j =
  of_nat (job_abs_deadline (jobs j))

choose_edf :: (JobId -> Job) -> Nat -> Schedule -> Time -> (List JobId) ->
              Option JobId
choose_edf jobs m sched t candidates =
  choose_min_metric (edf_metric jobs) jobs m sched t candidates

edf_generic_spec :: GenericSchedulingAlgorithm
edf_generic_spec =
  choose_edf

periodic_candidates_before :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId
                              -> Job) -> (List TaskId) -> PeriodicCodec ->
                              CandidateSource
periodic_candidates_before tasks offset jobs enumT codec _ _ _ t =
  enum_periodic_jobs_before tasks offset jobs enumT codec (S t)

generated_periodic_edf_schedule_upto :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (JobId -> Job) -> Time -> (List
                                        TaskId) -> PeriodicCodec -> Schedule
generated_periodic_edf_schedule_upto tasks offset jobs h enumT codec =
  generated_schedule edf_generic_spec
    (enum_candidates_of
      (enum_periodic_jobs_upto tasks offset jobs h enumT
        (periodic_finite_horizon_codec_of tasks offset jobs h codec)))
    jobs

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

critical_dbf_windows_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                             TaskId) -> Time -> List (Prod Time Time)
critical_dbf_windows_upto tasks offset enumT h =
  let {points = critical_dbf_points_upto tasks offset enumT h} in
  flat_map (\t1 ->
    map (\t2 -> Pair t1 t2)
      (filter (\t2 -> andb (leb t1 t2) (leb t2 h)) points))
    points

dbf_test_upto :: (TaskId -> Task) -> (List TaskId) -> Time -> Bool
dbf_test_upto tasks enumT h =
  forallb (\t -> leb (taskset_periodic_dbf tasks enumT t) t)
    (critical_dbf_points_upto tasks (\_ -> O) enumT h)

window_dbf_test_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                        TaskId) -> Time -> Bool
window_dbf_test_upto tasks offset enumT h =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      leb (taskset_periodic_dbf_window tasks offset enumT t1 t2) (sub t2 t1)})
    (critical_dbf_windows_upto tasks offset enumT h)

first_dbf_overload_upto :: (TaskId -> Task) -> (List TaskId) -> Time ->
                           Option Time
first_dbf_overload_upto tasks enumT h =
  find (\t -> negb (leb (taskset_periodic_dbf tasks enumT t) t))
    (critical_dbf_points_upto tasks (\_ -> O) enumT h)

first_window_dbf_overload_upto :: (TaskId -> Task) -> (TaskId -> Time) ->
                                  (List TaskId) -> Time -> Option
                                  (Prod Time Time)
first_window_dbf_overload_upto tasks offset enumT h =
  find (\w ->
    case w of {
     Pair t1 t2 ->
      negb
        (leb (taskset_periodic_dbf_window tasks offset enumT t1 t2)
          (sub t2 t1))})
    (critical_dbf_windows_upto tasks offset enumT h)

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

task_of_extracted :: ExtractedPeriodicTask -> Task
task_of_extracted _UU03c4_ =
  MkTask (extracted_task_cost _UU03c4_) (extracted_task_period _UU03c4_)
    (extracted_task_relative_deadline _UU03c4_)

default_extracted_periodic_task :: ExtractedPeriodicTask
default_extracted_periodic_task =
  MkExtractedPeriodicTask (S O) (S O) (S O) O

tasks_of_extracted_list :: (List ExtractedPeriodicTask) -> TaskId -> Task
tasks_of_extracted_list ts _UU03c4_ =
  task_of_extracted (nth _UU03c4_ ts default_extracted_periodic_task)

offset_of_extracted_list :: (List ExtractedPeriodicTask) -> TaskId -> Time
offset_of_extracted_list ts _UU03c4_ =
  extracted_task_offset (nth _UU03c4_ ts default_extracted_periodic_task)

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

offset_window_dbf_test_by_cutoff :: (TaskId -> Task) -> (TaskId -> Time) ->
                                    (List TaskId) -> Bool
offset_window_dbf_test_by_cutoff tasks offset enumT =
  window_dbf_test_upto tasks offset enumT
    (offset_window_dbf_cutoff_bound tasks offset enumT)

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

extracted_offset_window_dbf_test_upto :: (List ExtractedPeriodicTask) -> Time
                                         -> Bool
extracted_offset_window_dbf_test_upto ts h =
  window_dbf_test_upto (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts) h

extracted_offset_window_dbf_counterexample :: (List ExtractedPeriodicTask) ->
                                              Time -> Option (Prod Time Time)
extracted_offset_window_dbf_counterexample ts h =
  first_window_dbf_overload_upto (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts) h

extracted_offset_window_dbf_decide :: (List ExtractedPeriodicTask) -> Time ->
                                      Bool
extracted_offset_window_dbf_decide ts h =
  andb (extracted_taskset_wf ts) (extracted_offset_window_dbf_test_upto ts h)

extracted_offset_window_dbf_cutoff_bound :: (List ExtractedPeriodicTask) ->
                                            Time
extracted_offset_window_dbf_cutoff_bound ts =
  offset_window_dbf_cutoff_bound (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts)

extracted_offset_window_dbf_test_by_cutoff :: (List ExtractedPeriodicTask) ->
                                              Bool
extracted_offset_window_dbf_test_by_cutoff ts =
  offset_window_dbf_test_by_cutoff (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts)

extracted_offset_window_dbf_counterexample_by_cutoff :: (List
                                                        ExtractedPeriodicTask)
                                                        -> Option
                                                        (Prod Time Time)
extracted_offset_window_dbf_counterexample_by_cutoff ts =
  extracted_offset_window_dbf_counterexample ts
    (extracted_offset_window_dbf_cutoff_bound ts)

extracted_offset_window_dbf_decide_by_cutoff :: (List ExtractedPeriodicTask)
                                                -> Bool
extracted_offset_window_dbf_decide_by_cutoff ts =
  andb (extracted_taskset_wf ts)
    (extracted_offset_window_dbf_test_by_cutoff ts)

extracted_periodic_tasks :: (List ExtractedPeriodicTask) -> TaskId -> Task
extracted_periodic_tasks =
  tasks_of_extracted_list

extracted_periodic_offsets :: (List ExtractedPeriodicTask) -> TaskId -> Time
extracted_periodic_offsets =
  offset_of_extracted_list

extracted_periodic_jobs :: (List ExtractedPeriodicTask) -> JobId -> Job
extracted_periodic_jobs ts =
  canonical_periodic_jobs_from_enumT (extracted_periodic_tasks ts) (\_ -> O)
    (enumT_of_extracted_list ts)

extracted_offset_periodic_jobs :: (List ExtractedPeriodicTask) -> JobId ->
                                  Job
extracted_offset_periodic_jobs ts =
  canonical_periodic_jobs_from_enumT (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts) (enumT_of_extracted_list ts)

schedule_of_slots :: (List (Option JobId)) -> Schedule
schedule_of_slots slots t c =
  case eqb c O of {
   True -> nth t slots None;
   False -> None}

certified_service_prefix :: (List (Option JobId)) -> JobId -> Time -> Nat
certified_service_prefix slots j t =
  case t of {
   O -> O;
   S t' ->
    add (certified_service_prefix slots j t')
      (case nth t' slots None of {
        Some j' -> case eqb j j' of {
                    True -> S O;
                    False -> O};
        None -> O})}

certified_completed_by :: (JobId -> Job) -> (List (Option JobId)) -> JobId ->
                          Time -> Bool
certified_completed_by jobs slots j t =
  leb (job_cost (jobs j)) (certified_service_prefix slots j t)

check_prefix_completed_by :: (JobId -> Job) -> (EDFPrefixCert JobId) -> Bool
check_prefix_completed_by jobs c =
  forallb (\jt ->
    case jt of {
     Pair j t -> certified_completed_by jobs (prefix_slots c) j t})
    (combine (prefix_basis_jobs c) (prefix_completed_by c))

check_prefix_backlog_row :: (JobId -> Job) -> (List (Option JobId)) -> Time
                            -> (List JobId) -> (List Bool) -> Bool
check_prefix_backlog_row jobs slots release_time basis row =
  case basis of {
   Nil -> case row of {
           Nil -> True;
           Cons _ _ -> False};
   Cons jj basis' ->
    case row of {
     Nil -> False;
     Cons b row' ->
      andb
        (case b of {
          True -> certified_completed_by jobs slots jj release_time;
          False -> True})
        (check_prefix_backlog_row jobs slots release_time basis' row')}}

check_prefix_backlog_rows_with_basis :: (JobId -> Job) -> (List
                                        (Option JobId)) -> (List JobId) ->
                                        (List JobId) -> (List (List Bool)) ->
                                        Bool
check_prefix_backlog_rows_with_basis jobs slots row_basis column_basis rows =
  case row_basis of {
   Nil -> case rows of {
           Nil -> True;
           Cons _ _ -> False};
   Cons ji basis' ->
    case rows of {
     Nil -> False;
     Cons row rows' ->
      andb
        (check_prefix_backlog_row jobs slots (job_release (jobs ji))
          column_basis row)
        (check_prefix_backlog_rows_with_basis jobs slots basis' column_basis
          rows')}}

check_prefix_backlog_rows :: (JobId -> Job) -> (List (Option JobId)) -> (List
                             JobId) -> (List (List Bool)) -> Bool
check_prefix_backlog_rows jobs slots basis rows =
  check_prefix_backlog_rows_with_basis jobs slots basis basis rows

check_prefix_backlog_matrix :: (JobId -> Job) -> (EDFPrefixCert JobId) ->
                               Bool
check_prefix_backlog_matrix jobs c =
  check_prefix_backlog_rows jobs (prefix_slots c) (prefix_basis_jobs c)
    (prefix_backlog_free_matrix c)

check_prefix_cert_semantic :: (JobId -> Job) -> (EDFPrefixCert JobId) -> Bool
check_prefix_cert_semantic jobs c =
  andb (andb (check_prefix_cert c) (check_prefix_completed_by jobs c))
    (check_prefix_backlog_matrix jobs c)

option_job_eqb :: (Option JobId) -> (Option JobId) -> Bool
option_job_eqb x y =
  case x of {
   Some jx -> case y of {
               Some jy -> eqb jx jy;
               None -> False};
   None -> case y of {
            Some _ -> False;
            None -> True}}

check_prefix_slots_match_generated_edf_fast :: (TaskId -> Task) -> (TaskId ->
                                               Time) -> (JobId -> Job) ->
                                               (List TaskId) -> PeriodicCodec
                                               -> (EDFPrefixCert JobId) ->
                                               Bool
check_prefix_slots_match_generated_edf_fast tasks offset jobs enumT codec c =
  andb (check_prefix_cert c)
    (forallb (\t ->
      option_job_eqb (nth t (prefix_slots c) None)
        (choose_edf jobs (S O) (schedule_of_slots (prefix_slots c)) t
          (periodic_candidates_before tasks offset jobs enumT codec jobs (S
            O) (schedule_of_slots (prefix_slots c)) t)))
      (seq O (prefix_horizon c)))

index_of_job :: JobId -> (List JobId) -> Option Nat
index_of_job j basis =
  case basis of {
   Nil -> None;
   Cons j' basis' ->
    case eqb j j' of {
     True -> Some O;
     False -> option_map (\x -> S x) (index_of_job j basis')}}

check_job_in_basis :: (List JobId) -> JobId -> Bool
check_job_in_basis basis j =
  case index_of_job j basis of {
   Some _ -> True;
   None -> False}

check_prefix_backlog_pair :: (EDFPrefixCert JobId) -> JobId -> JobId -> Bool
check_prefix_backlog_pair c target earlier =
  case index_of_job target (prefix_basis_jobs c) of {
   Some i ->
    case index_of_job earlier (prefix_basis_jobs c) of {
     Some k ->
      case nth_error (prefix_backlog_free_matrix c) i of {
       Some row -> case nth_error row k of {
                    Some b -> b;
                    None -> False};
       None -> False};
     None -> False};
   None -> False}

check_prefix_backlog_free_before_release :: (EDFPrefixCert JobId) -> JobId ->
                                            (List JobId) -> Bool
check_prefix_backlog_free_before_release c target relevant_jobs =
  andb (check_job_in_basis (prefix_basis_jobs c) target)
    (forallb (check_prefix_backlog_pair c target) relevant_jobs)

check_transport_job_witness :: (EDFTransportCert JobId) -> JobId -> Bool
check_transport_job_witness c j =
  check_job_in_basis (transport_basis_jobs c) j

check_transport_jobs_witness :: (EDFTransportCert JobId) -> (List JobId) ->
                                Bool
check_transport_jobs_witness c jobs =
  forallb (check_transport_job_witness c) jobs

periodic_transport_residue_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                   (JobId -> Job) -> (List TaskId) ->
                                   PeriodicCodec -> Time -> List JobId
periodic_transport_residue_jobs tasks offset jobs enumT codec period =
  flat_map (\_UU03c4_ ->
    map (global_periodic_job_id_of tasks offset jobs codec _UU03c4_)
      (seq O period))
    enumT

check_periodic_transport_residue_coverage :: (EDFTransportCert JobId) ->
                                             (List JobId) -> Bool
check_periodic_transport_residue_coverage transport_cert residue_jobs =
  andb (ltb O (transport_period transport_cert))
    (check_transport_jobs_witness transport_cert residue_jobs)

check_transport_residue_shifts :: (EDFTransportCert JobId) -> Bool
check_transport_residue_shifts transport_cert =
  forallb (\shift -> eqb shift (transport_period transport_cert))
    (transport_job_shift transport_cert)

data EDFWindowTransportPairCert =
   Build_EDFWindowTransportPairCert JobId JobId Time

window_target_earlier_job :: EDFWindowTransportPairCert -> JobId
window_target_earlier_job e =
  case e of {
   Build_EDFWindowTransportPairCert window_target_earlier_job0 _ _ ->
    window_target_earlier_job0}

window_rep_earlier_job :: EDFWindowTransportPairCert -> JobId
window_rep_earlier_job e =
  case e of {
   Build_EDFWindowTransportPairCert _ window_rep_earlier_job0 _ ->
    window_rep_earlier_job0}

window_transport_delta :: EDFWindowTransportPairCert -> Time
window_transport_delta e =
  case e of {
   Build_EDFWindowTransportPairCert _ _ window_transport_delta0 ->
    window_transport_delta0}

data EDFWindowTransportTargetCert =
   Build_EDFWindowTransportTargetCert JobId Nat Nat (List
                                                    EDFWindowTransportPairCert)

window_transport_target_job :: EDFWindowTransportTargetCert -> JobId
window_transport_target_job e =
  case e of {
   Build_EDFWindowTransportTargetCert window_transport_target_job0 _ _ _ ->
    window_transport_target_job0}

window_transport_class_id :: EDFWindowTransportTargetCert -> Nat
window_transport_class_id e =
  case e of {
   Build_EDFWindowTransportTargetCert _ window_transport_class_id0 _ _ ->
    window_transport_class_id0}

window_transport_shift :: EDFWindowTransportTargetCert -> Nat
window_transport_shift e =
  case e of {
   Build_EDFWindowTransportTargetCert _ _ window_transport_shift0 _ ->
    window_transport_shift0}

window_transport_pairs :: EDFWindowTransportTargetCert -> List
                          EDFWindowTransportPairCert
window_transport_pairs e =
  case e of {
   Build_EDFWindowTransportTargetCert _ _ _ window_transport_pairs0 ->
    window_transport_pairs0}

check_shifted_job_relation :: (JobId -> Job) -> JobId -> JobId ->
                              EDFWindowTransportPairCert -> Bool
check_shifted_job_relation jobs rep target p =
  let {delta = window_transport_delta p} in
  andb
    (andb
      (andb
        (eqb (job_release (jobs target))
          (add (job_release (jobs rep)) delta))
        (eqb (job_abs_deadline (jobs target))
          (add (job_abs_deadline (jobs rep)) delta)))
      (eqb (job_release (jobs (window_target_earlier_job p)))
        (add (job_release (jobs (window_rep_earlier_job p))) delta)))
    (eqb (job_abs_deadline (jobs (window_target_earlier_job p)))
      (add (job_abs_deadline (jobs (window_rep_earlier_job p))) delta))

check_window_transport_target :: (JobId -> Job) -> (EDFTransportCert 
                                 JobId) -> EDFWindowTransportTargetCert ->
                                 Bool
check_window_transport_target jobs transport_cert target_cert =
  case index_of_job (window_transport_target_job target_cert)
         (transport_basis_jobs transport_cert) of {
   Some i ->
    case nth_error (transport_job_class transport_cert) i of {
     Some class_id ->
      case nth_error (transport_job_shift transport_cert) i of {
       Some shift ->
        case nth_error (transport_classes transport_cert)
               (window_transport_class_id target_cert) of {
         Some cls ->
          andb
            (andb (eqb class_id (window_transport_class_id target_cert))
              (eqb shift (window_transport_shift target_cert)))
            (forallb
              (check_shifted_job_relation jobs (transport_rep_job cls)
                (window_transport_target_job target_cert))
              (window_transport_pairs target_cert));
         None -> False};
       None -> False};
     None -> False};
   None -> False}

check_window_transport_targets :: (JobId -> Job) -> (EDFTransportCert 
                                  JobId) -> (List
                                  EDFWindowTransportTargetCert) -> Bool
check_window_transport_targets jobs transport_cert target_certs =
  forallb (check_window_transport_target jobs transport_cert) target_certs

check_window_transport_target_entry :: (JobId -> Job) -> (EDFTransportCert
                                       JobId) -> Nat -> Nat -> Nat ->
                                       EDFWindowTransportTargetCert -> Bool
check_window_transport_target_entry jobs transport_cert target class_id shift target_cert =
  andb
    (andb
      (andb (eqb (window_transport_target_job target_cert) target)
        (eqb (window_transport_class_id target_cert) class_id))
      (eqb (window_transport_shift target_cert) shift))
    (check_window_transport_target jobs transport_cert target_cert)

check_window_transport_target_rows_complete :: (JobId -> Job) ->
                                               (EDFTransportCert JobId) ->
                                               (List
                                               EDFWindowTransportTargetCert)
                                               -> (List JobId) -> (List 
                                               Nat) -> (List Nat) -> Bool
check_window_transport_target_rows_complete jobs transport_cert target_certs basis classes shifts =
  case basis of {
   Nil ->
    case classes of {
     Nil -> case shifts of {
             Nil -> True;
             Cons _ _ -> False};
     Cons _ _ -> False};
   Cons target basis' ->
    case classes of {
     Nil -> False;
     Cons class_id classes' ->
      case shifts of {
       Nil -> False;
       Cons shift shifts' ->
        case nth_error (transport_classes transport_cert) class_id of {
         Some _ ->
          andb
            (existsb
              (check_window_transport_target_entry jobs transport_cert target
                class_id shift)
              target_certs)
            (check_window_transport_target_rows_complete jobs transport_cert
              target_certs basis' classes' shifts');
         None -> False}}}}

check_window_transport_targets_complete :: (JobId -> Job) ->
                                           (EDFTransportCert JobId) -> (List
                                           EDFWindowTransportTargetCert) ->
                                           Bool
check_window_transport_targets_complete jobs transport_cert target_certs =
  andb (check_window_transport_targets jobs transport_cert target_certs)
    (check_window_transport_target_rows_complete jobs transport_cert
      target_certs (transport_basis_jobs transport_cert)
      (transport_job_class transport_cert)
      (transport_job_shift transport_cert))

window_target_candidate_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (JobId -> Job) -> (List TaskId) ->
                                PeriodicCodec -> JobId -> List JobId
window_target_candidate_jobs tasks offset jobs enumT codec target =
  let {h = S (job_abs_deadline (jobs target))} in
  enum_periodic_jobs_upto tasks offset jobs h enumT
    (periodic_finite_horizon_codec_of tasks offset jobs h codec)

window_target_relevant_earlier_jobs :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (JobId -> Job) -> (List TaskId) ->
                                       PeriodicCodec -> JobId -> List 
                                       JobId
window_target_relevant_earlier_jobs tasks offset jobs enumT codec target =
  filter (\x ->
    andb (ltb (job_release (jobs x)) (job_release (jobs target)))
      (leb (job_abs_deadline (jobs x)) (job_abs_deadline (jobs target))))
    (window_target_candidate_jobs tasks offset jobs enumT codec target)

check_window_target_periodic :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (JobId -> Job) -> (List TaskId) ->
                                PeriodicCodec -> JobId -> Bool
check_window_target_periodic tasks offset jobs enumT codec target =
  existsb (eqb target)
    (window_target_candidate_jobs tasks offset jobs enumT codec target)

check_window_rep_earlier_membership :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (JobId -> Job) -> (List TaskId) ->
                                       PeriodicCodec -> JobId ->
                                       EDFWindowTransportPairCert -> Bool
check_window_rep_earlier_membership tasks offset jobs enumT codec rep p =
  existsb (eqb (window_rep_earlier_job p))
    (window_target_relevant_earlier_jobs tasks offset jobs enumT codec rep)

check_window_target_rep_earlier_membership :: (TaskId -> Task) -> (TaskId ->
                                              Time) -> (JobId -> Job) ->
                                              (List TaskId) -> PeriodicCodec
                                              -> JobId ->
                                              EDFWindowTransportTargetCert ->
                                              Bool
check_window_target_rep_earlier_membership tasks offset jobs enumT codec rep target_cert =
  forallb
    (check_window_rep_earlier_membership tasks offset jobs enumT codec rep)
    (window_transport_pairs target_cert)

check_window_generated_pair_semantics :: (TaskId -> Task) -> (TaskId -> Time)
                                         -> (JobId -> Job) -> (List TaskId)
                                         -> PeriodicCodec ->
                                         (EDFTransportCert JobId) ->
                                         EDFWindowTransportTargetCert -> Bool
check_window_generated_pair_semantics tasks offset jobs enumT codec transport_cert target_cert =
  case nth_error (transport_classes transport_cert)
         (window_transport_class_id target_cert) of {
   Some cls ->
    andb
      (check_window_target_periodic tasks offset jobs enumT codec
        (window_transport_target_job target_cert))
      (check_window_target_rep_earlier_membership tasks offset jobs enumT
        codec (transport_rep_job cls) target_cert);
   None -> False}

check_window_generated_pair_semantics_all :: (TaskId -> Task) -> (TaskId ->
                                             Time) -> (JobId -> Job) -> (List
                                             TaskId) -> PeriodicCodec ->
                                             (EDFTransportCert JobId) ->
                                             (List
                                             EDFWindowTransportTargetCert) ->
                                             Bool
check_window_generated_pair_semantics_all tasks offset jobs enumT codec transport_cert target_certs =
  forallb
    (check_window_generated_pair_semantics tasks offset jobs enumT codec
      transport_cert)
    target_certs

check_generated_window_pair_target_completed :: (TaskId -> Task) -> (TaskId
                                                -> Time) -> (JobId -> Job) ->
                                                (List TaskId) ->
                                                PeriodicCodec -> JobId ->
                                                EDFWindowTransportPairCert ->
                                                Bool
check_generated_window_pair_target_completed tasks offset jobs enumT codec target p =
  leb (job_cost (jobs (window_target_earlier_job p)))
    (service_job (S O)
      (generated_periodic_edf_schedule_upto tasks offset jobs (S
        (job_abs_deadline (jobs target))) enumT codec)
      (window_target_earlier_job p) (job_release (jobs target)))

check_window_generated_pair_completion :: (TaskId -> Task) -> (TaskId ->
                                          Time) -> (JobId -> Job) -> (List
                                          TaskId) -> PeriodicCodec ->
                                          EDFWindowTransportTargetCert ->
                                          Bool
check_window_generated_pair_completion tasks offset jobs enumT codec target_cert =
  forallb
    (check_generated_window_pair_target_completed tasks offset jobs enumT
      codec (window_transport_target_job target_cert))
    (window_transport_pairs target_cert)

check_window_generated_pair_completion_all :: (TaskId -> Task) -> (TaskId ->
                                              Time) -> (JobId -> Job) ->
                                              (List TaskId) -> PeriodicCodec
                                              -> (List
                                              EDFWindowTransportTargetCert)
                                              -> Bool
check_window_generated_pair_completion_all tasks offset jobs enumT codec target_certs =
  forallb
    (check_window_generated_pair_completion tasks offset jobs enumT codec)
    target_certs

check_window_transport_pair_for_target_earlier :: (JobId -> Job) -> JobId ->
                                                  JobId -> JobId ->
                                                  EDFWindowTransportPairCert
                                                  -> Bool
check_window_transport_pair_for_target_earlier jobs rep target x p =
  andb
    (andb
      (andb (eqb (window_target_earlier_job p) x)
        (ltb (job_release (jobs (window_rep_earlier_job p)))
          (job_release (jobs rep))))
      (leb (job_abs_deadline (jobs (window_rep_earlier_job p)))
        (job_abs_deadline (jobs rep))))
    (check_shifted_job_relation jobs rep target p)

check_window_target_pair_coverage :: (JobId -> Job) -> JobId ->
                                     EDFWindowTransportTargetCert -> (List
                                     JobId) -> Bool
check_window_target_pair_coverage jobs rep target_cert target_earlier_jobs =
  forallb (\x ->
    existsb
      (check_window_transport_pair_for_target_earlier jobs rep
        (window_transport_target_job target_cert) x)
      (window_transport_pairs target_cert))
    target_earlier_jobs

check_window_transport_target_complete_with_pairs :: (TaskId -> Task) ->
                                                     (TaskId -> Time) ->
                                                     (JobId -> Job) -> (List
                                                     TaskId) -> PeriodicCodec
                                                     -> (EDFTransportCert
                                                     JobId) ->
                                                     EDFWindowTransportTargetCert
                                                     -> Bool
check_window_transport_target_complete_with_pairs tasks offset jobs enumT codec transport_cert target_cert =
  case nth_error (transport_classes transport_cert)
         (window_transport_class_id target_cert) of {
   Some cls ->
    andb (check_window_transport_target jobs transport_cert target_cert)
      (check_window_target_pair_coverage jobs (transport_rep_job cls)
        target_cert
        (window_target_relevant_earlier_jobs tasks offset jobs enumT codec
          (window_transport_target_job target_cert)));
   None -> False}

check_window_transport_targets_complete_with_pairs :: (TaskId -> Task) ->
                                                      (TaskId -> Time) ->
                                                      (JobId -> Job) -> (List
                                                      TaskId) ->
                                                      PeriodicCodec ->
                                                      (EDFTransportCert
                                                      JobId) -> (List
                                                      EDFWindowTransportTargetCert)
                                                      -> Bool
check_window_transport_targets_complete_with_pairs tasks offset jobs enumT codec transport_cert target_certs =
  andb
    (forallb
      (check_window_transport_target_complete_with_pairs tasks offset jobs
        enumT codec transport_cert)
      target_certs)
    (check_window_transport_target_rows_complete jobs transport_cert
      target_certs (transport_basis_jobs transport_cert)
      (transport_job_class transport_cert)
      (transport_job_shift transport_cert))

check_jobid_not_in :: JobId -> (List JobId) -> Bool
check_jobid_not_in j xs =
  forallb (\x -> negb (eqb j x)) xs

check_jobid_list_nodup :: (List JobId) -> Bool
check_jobid_list_nodup xs =
  case xs of {
   Nil -> True;
   Cons x xs' -> andb (check_jobid_not_in x xs') (check_jobid_list_nodup xs')}

check_transport_basis_nodup :: (EDFTransportCert JobId) -> Bool
check_transport_basis_nodup transport_cert =
  check_jobid_list_nodup (transport_basis_jobs transport_cert)

check_transport_class_rep_periodic_generated :: (TaskId -> Task) -> (TaskId
                                                -> Time) -> (JobId -> Job) ->
                                                (List TaskId) ->
                                                PeriodicCodec ->
                                                (EDFTransportClass JobId) ->
                                                Bool
check_transport_class_rep_periodic_generated tasks offset jobs enumT codec cls =
  check_window_target_periodic tasks offset jobs enumT codec
    (transport_rep_job cls)

check_transport_classes_rep_periodic_generated :: (TaskId -> Task) -> (TaskId
                                                  -> Time) -> (JobId -> Job)
                                                  -> (List TaskId) ->
                                                  PeriodicCodec -> (List
                                                  (EDFTransportClass JobId))
                                                  -> Bool
check_transport_classes_rep_periodic_generated tasks offset jobs enumT codec classes =
  forallb
    (check_transport_class_rep_periodic_generated tasks offset jobs enumT
      codec)
    classes

check_transport_class_rep_backlog :: (EDFPrefixCert JobId) ->
                                     (EDFTransportClass JobId) -> (List
                                     JobId) -> Bool
check_transport_class_rep_backlog prefix_cert cls relevant_jobs =
  check_prefix_backlog_free_before_release prefix_cert
    (transport_rep_job cls) relevant_jobs

check_transport_classes_rep_backlog :: (EDFPrefixCert JobId) -> (List
                                       (EDFTransportClass JobId)) -> (List
                                       (List JobId)) -> Bool
check_transport_classes_rep_backlog prefix_cert classes class_relevant_jobs =
  case classes of {
   Nil -> case class_relevant_jobs of {
           Nil -> True;
           Cons _ _ -> False};
   Cons cls classes' ->
    case class_relevant_jobs of {
     Nil -> False;
     Cons relevant relevant' ->
      andb (check_transport_class_rep_backlog prefix_cert cls relevant)
        (check_transport_classes_rep_backlog prefix_cert classes' relevant')}}

transport_class_rep_relevant_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                     (JobId -> Job) -> (List TaskId) ->
                                     PeriodicCodec -> (EDFTransportClass
                                     JobId) -> List JobId
transport_class_rep_relevant_jobs tasks offset jobs enumT codec cls =
  window_target_relevant_earlier_jobs tasks offset jobs enumT codec
    (transport_rep_job cls)

transport_classes_rep_relevant_jobs :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (JobId -> Job) -> (List TaskId) ->
                                       PeriodicCodec -> (List
                                       (EDFTransportClass JobId)) -> List
                                       (List JobId)
transport_classes_rep_relevant_jobs tasks offset jobs enumT codec classes =
  map (transport_class_rep_relevant_jobs tasks offset jobs enumT codec)
    classes

check_transport_class_rep_backlog_generated :: (TaskId -> Task) -> (TaskId ->
                                               Time) -> (JobId -> Job) ->
                                               (List TaskId) -> PeriodicCodec
                                               -> (EDFPrefixCert JobId) ->
                                               (EDFTransportClass JobId) ->
                                               Bool
check_transport_class_rep_backlog_generated tasks offset jobs enumT codec prefix_cert cls =
  check_transport_class_rep_backlog prefix_cert cls
    (transport_class_rep_relevant_jobs tasks offset jobs enumT codec cls)

check_transport_classes_rep_backlog_generated :: (TaskId -> Task) -> (TaskId
                                                 -> Time) -> (JobId -> Job)
                                                 -> (List TaskId) ->
                                                 PeriodicCodec ->
                                                 (EDFPrefixCert JobId) ->
                                                 (List
                                                 (EDFTransportClass JobId))
                                                 -> Bool
check_transport_classes_rep_backlog_generated tasks offset jobs enumT codec prefix_cert classes =
  case classes of {
   Nil -> True;
   Cons cls classes' ->
    andb
      (check_transport_class_rep_backlog_generated tasks offset jobs enumT
        codec prefix_cert cls)
      (check_transport_classes_rep_backlog_generated tasks offset jobs enumT
        codec prefix_cert classes')}

post_reset_target_candidate_horizon :: (TaskId -> Task) -> (List TaskId) ->
                                       Time
post_reset_target_candidate_horizon tasks enumT =
  add (mul (S (S O)) (periodic_hyperperiod tasks enumT))
    (periodic_max_relative_deadline tasks enumT)

post_reset_window_targets_of_certs :: (List EDFWindowTransportTargetCert) ->
                                      List JobId
post_reset_window_targets_of_certs target_certs =
  map window_transport_target_job target_certs

post_reset_window_target_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                 (JobId -> Job) -> (List TaskId) ->
                                 PeriodicCodec -> List JobId
post_reset_window_target_jobs tasks offset jobs enumT codec =
  enum_periodic_jobs_before tasks offset jobs enumT codec
    (post_reset_target_candidate_horizon tasks enumT)

check_post_reset_window_target_basis_coverage :: (EDFTransportCert JobId) ->
                                                 (List
                                                 EDFWindowTransportTargetCert)
                                                 -> Bool
check_post_reset_window_target_basis_coverage transport_cert target_certs =
  check_transport_jobs_witness transport_cert
    (post_reset_window_targets_of_certs target_certs)

check_post_reset_target_list_complete :: (List JobId) -> (List
                                         EDFWindowTransportTargetCert) ->
                                         Bool
check_post_reset_target_list_complete candidate_targets target_certs =
  forallb
    (check_job_in_basis (post_reset_window_targets_of_certs target_certs))
    candidate_targets

check_post_reset_window_targets_complete_with_pairs :: (TaskId -> Task) ->
                                                       (TaskId -> Time) ->
                                                       (JobId -> Job) ->
                                                       (List TaskId) ->
                                                       PeriodicCodec ->
                                                       (EDFTransportCert
                                                       JobId) -> (List
                                                       EDFWindowTransportTargetCert)
                                                       -> Bool
check_post_reset_window_targets_complete_with_pairs tasks offset jobs enumT codec transport_cert target_certs =
  andb
    (andb
      (check_window_transport_targets_complete_with_pairs tasks offset jobs
        enumT codec transport_cert target_certs)
      (check_window_generated_pair_semantics_all tasks offset jobs enumT
        codec transport_cert target_certs))
    (check_window_generated_pair_completion_all tasks offset jobs enumT codec
      target_certs)

check_hyperperiod_delta_multiple :: (TaskId -> Task) -> (List TaskId) -> Time
                                    -> Bool
check_hyperperiod_delta_multiple tasks enumT delta =
  eqb delta
    (mul (periodic_hyperperiod tasks enumT)
      (div delta (periodic_hyperperiod tasks enumT)))

check_hyperperiod_shifted_service_pair :: (TaskId -> Task) -> (List TaskId)
                                          -> (JobId -> Job) -> JobId -> JobId
                                          -> JobId -> JobId -> Time -> Bool
check_hyperperiod_shifted_service_pair tasks enumT jobs target x target0 x0 delta =
  andb
    (andb
      (andb
        (andb
          (andb (check_hyperperiod_delta_multiple tasks enumT delta)
            (eqb (job_release (jobs target))
              (add (job_release (jobs target0)) delta)))
          (eqb (job_abs_deadline (jobs target))
            (add (job_abs_deadline (jobs target0)) delta)))
        (eqb (job_release (jobs x)) (add (job_release (jobs x0)) delta)))
      (eqb (job_abs_deadline (jobs x))
        (add (job_abs_deadline (jobs x0)) delta)))
    (eqb (job_cost (jobs x)) (job_cost (jobs x0)))

check_hyperperiod_block_source_pair :: (TaskId -> Task) -> (List TaskId) ->
                                       (JobId -> Job) -> JobId -> JobId ->
                                       JobId -> JobId ->
                                       EDFWindowTransportTargetCert ->
                                       EDFWindowTransportPairCert -> Bool
check_hyperperiod_block_source_pair tasks enumT jobs target x target0 x0 target_cert p =
  andb
    (andb (eqb (window_transport_target_job target_cert) target0)
      (eqb (window_target_earlier_job p) x0))
    (check_hyperperiod_shifted_service_pair tasks enumT jobs target x target0
      x0 (window_transport_delta p))

check_hyperperiod_block_source_pair_in_cert :: (TaskId -> Task) -> (List
                                               TaskId) -> (JobId -> Job) ->
                                               JobId -> JobId -> JobId ->
                                               JobId ->
                                               EDFWindowTransportTargetCert
                                               -> Bool
check_hyperperiod_block_source_pair_in_cert tasks enumT jobs target x target0 x0 target_cert =
  existsb
    (check_hyperperiod_block_source_pair tasks enumT jobs target x target0 x0
      target_cert)
    (window_transport_pairs target_cert)

check_hyperperiod_block_source_pair_in_certs :: (TaskId -> Task) -> (List
                                                TaskId) -> (JobId -> Job) ->
                                                JobId -> JobId -> JobId ->
                                                JobId -> (List
                                                EDFWindowTransportTargetCert)
                                                -> Bool
check_hyperperiod_block_source_pair_in_certs tasks enumT jobs target x target0 x0 target_certs =
  existsb
    (check_hyperperiod_block_source_pair_in_cert tasks enumT jobs target x
      target0 x0)
    target_certs

data PeriodicEDFCheckedSidecarCert =
   Build_PeriodicEDFCheckedSidecarCert (List JobId) (List (List JobId)) 
 (List EDFWindowTransportTargetCert) (List EDFWindowTransportTargetCert)

checked_class_relevant_jobs :: PeriodicEDFCheckedSidecarCert -> List
                               (List JobId)
checked_class_relevant_jobs p =
  case p of {
   Build_PeriodicEDFCheckedSidecarCert _ checked_class_relevant_jobs0 _ _ ->
    checked_class_relevant_jobs0}

checked_window_target_certs :: PeriodicEDFCheckedSidecarCert -> List
                               EDFWindowTransportTargetCert
checked_window_target_certs p =
  case p of {
   Build_PeriodicEDFCheckedSidecarCert _ _ checked_window_target_certs0 _ ->
    checked_window_target_certs0}

checked_post_reset_window_target_certs :: PeriodicEDFCheckedSidecarCert ->
                                          List EDFWindowTransportTargetCert
checked_post_reset_window_target_certs p =
  case p of {
   Build_PeriodicEDFCheckedSidecarCert _ _ _
    checked_post_reset_window_target_certs0 ->
    checked_post_reset_window_target_certs0}

extracted_taskset_nonempty :: (List ExtractedPeriodicTask) -> Bool
extracted_taskset_nonempty ts =
  ltb O (length ts)

extracted_periodic_codec :: (List ExtractedPeriodicTask) -> PeriodicCodec
extracted_periodic_codec ts =
  case ts of {
   Nil -> (\_ _ -> O);
   Cons e l ->
    zero_offset_periodic_codec_of_tasks (extracted_periodic_tasks (Cons e l))
      (enumT_of_extracted_list (Cons e l))}

extracted_offset_periodic_codec :: (List ExtractedPeriodicTask) ->
                                   PeriodicCodec
extracted_offset_periodic_codec ts =
  case ts of {
   Nil -> (\_ _ -> O);
   Cons e l ->
    periodic_codec_of_enumT (extracted_periodic_tasks (Cons e l))
      (extracted_periodic_offsets (Cons e l))
      (enumT_of_extracted_list (Cons e l))}

check_periodic_hyperperiod_state_reset :: (TaskId -> Task) -> (TaskId ->
                                          Time) -> (JobId -> Job) -> (List
                                          TaskId) -> PeriodicCodec ->
                                          (EDFPrefixCert JobId) -> Time ->
                                          Bool
check_periodic_hyperperiod_state_reset tasks offset jobs enumT codec prefix_cert hyperperiod =
  forallb (\j ->
    certified_completed_by jobs (prefix_slots prefix_cert) j hyperperiod)
    (enum_periodic_jobs_before tasks offset jobs enumT codec hyperperiod)

check_transport_period_is_hyperperiod :: (TaskId -> Task) -> (List TaskId) ->
                                         (EDFTransportCert JobId) -> Bool
check_transport_period_is_hyperperiod tasks enumT transport_cert =
  eqb (transport_period transport_cert) (periodic_hyperperiod tasks enumT)

check_prefix_horizon_covers_hyperperiod :: (TaskId -> Task) -> (List 
                                           TaskId) -> (EDFPrefixCert 
                                           JobId) -> Bool
check_prefix_horizon_covers_hyperperiod tasks enumT prefix_cert =
  leb (periodic_hyperperiod tasks enumT) (prefix_horizon prefix_cert)

post_reset_window_horizon :: (TaskId -> Task) -> (List TaskId) -> Time
post_reset_window_horizon tasks enumT =
  add (mul (S (S O)) (periodic_hyperperiod tasks enumT))
    (periodic_max_relative_deadline tasks enumT)

check_prefix_horizon_covers_post_reset_window :: (TaskId -> Task) -> (List
                                                 TaskId) -> (EDFPrefixCert
                                                 JobId) -> Bool
check_prefix_horizon_covers_post_reset_window tasks enumT prefix_cert =
  leb (post_reset_window_horizon tasks enumT) (prefix_horizon prefix_cert)

check_periodic_edf_checked_sidecar_with_jobs :: (List ExtractedPeriodicTask)
                                                -> (TaskId -> Time) -> (JobId
                                                -> Job) -> PeriodicCodec ->
                                                (EDFInfiniteCert JobId) ->
                                                PeriodicEDFCheckedSidecarCert
                                                -> Bool
check_periodic_edf_checked_sidecar_with_jobs ts offset jobs codec cert sidecar =
  andb
    (andb
      (andb
        (andb
          (andb
            (andb
              (andb
                (andb
                  (andb
                    (andb
                      (andb
                        (andb
                          (andb
                            (andb
                              (andb
                                (andb
                                  (andb
                                    (andb
                                      (andb
                                        (check_prefix_cert_semantic jobs
                                          (cert_prefix cert))
                                        (check_prefix_slots_match_generated_edf_fast
                                          (extracted_periodic_tasks ts)
                                          offset jobs
                                          (enumT_of_extracted_list ts) codec
                                          (cert_prefix cert)))
                                      (check_periodic_hyperperiod_state_reset
                                        (extracted_periodic_tasks ts) offset
                                        jobs (enumT_of_extracted_list ts)
                                        codec (cert_prefix cert)
                                        (periodic_hyperperiod
                                          (extracted_periodic_tasks ts)
                                          (enumT_of_extracted_list ts))))
                                    (check_transport_period_is_hyperperiod
                                      (extracted_periodic_tasks ts)
                                      (enumT_of_extracted_list ts)
                                      (cert_transport cert)))
                                  (check_prefix_horizon_covers_hyperperiod
                                    (extracted_periodic_tasks ts)
                                    (enumT_of_extracted_list ts)
                                    (cert_prefix cert)))
                                (check_prefix_horizon_covers_post_reset_window
                                  (extracted_periodic_tasks ts)
                                  (enumT_of_extracted_list ts)
                                  (cert_prefix cert)))
                              (check_transport_cert (cert_transport cert)))
                            (check_transport_basis_nodup
                              (cert_transport cert)))
                          (check_transport_classes_rep_backlog
                            (cert_prefix cert)
                            (transport_classes (cert_transport cert))
                            (checked_class_relevant_jobs sidecar)))
                        (check_transport_classes_rep_backlog_generated
                          (extracted_periodic_tasks ts) offset jobs
                          (enumT_of_extracted_list ts) codec
                          (cert_prefix cert)
                          (transport_classes (cert_transport cert))))
                      (check_transport_classes_rep_periodic_generated
                        (extracted_periodic_tasks ts) offset jobs
                        (enumT_of_extracted_list ts) codec
                        (transport_classes (cert_transport cert))))
                    (check_periodic_transport_residue_coverage
                      (cert_transport cert)
                      (periodic_transport_residue_jobs
                        (extracted_periodic_tasks ts) offset jobs
                        (enumT_of_extracted_list ts) codec
                        (transport_period (cert_transport cert)))))
                  (check_transport_residue_shifts (cert_transport cert)))
                (check_window_transport_targets_complete_with_pairs
                  (extracted_periodic_tasks ts) offset jobs
                  (enumT_of_extracted_list ts) codec (cert_transport cert)
                  (checked_window_target_certs sidecar)))
              (check_window_generated_pair_semantics_all
                (extracted_periodic_tasks ts) offset jobs
                (enumT_of_extracted_list ts) codec (cert_transport cert)
                (checked_window_target_certs sidecar)))
            (check_window_generated_pair_completion_all
              (extracted_periodic_tasks ts) offset jobs
              (enumT_of_extracted_list ts) codec
              (checked_window_target_certs sidecar)))
          (check_post_reset_window_targets_complete_with_pairs
            (extracted_periodic_tasks ts) offset jobs
            (enumT_of_extracted_list ts) codec (cert_transport cert)
            (checked_post_reset_window_target_certs sidecar)))
        (check_post_reset_window_target_basis_coverage (cert_transport cert)
          (checked_post_reset_window_target_certs sidecar)))
      (check_post_reset_target_list_complete
        (post_reset_window_target_jobs (extracted_periodic_tasks ts) offset
          jobs (enumT_of_extracted_list ts) codec)
        (checked_post_reset_window_target_certs sidecar)))
    (edf_schedulability_decide ts)

check_periodic_edf_checked_sidecar :: (List ExtractedPeriodicTask) ->
                                      PeriodicCodec -> (EDFInfiniteCert
                                      JobId) -> PeriodicEDFCheckedSidecarCert
                                      -> Bool
check_periodic_edf_checked_sidecar ts codec cert sidecar =
  check_periodic_edf_checked_sidecar_with_jobs ts (\_ -> O)
    (extracted_periodic_jobs ts) codec cert sidecar

check_periodic_edf_checked_sidecar_extracted :: (List ExtractedPeriodicTask)
                                                -> (EDFInfiniteCert JobId) ->
                                                PeriodicEDFCheckedSidecarCert
                                                -> Bool
check_periodic_edf_checked_sidecar_extracted ts cert sidecar =
  andb (extracted_taskset_nonempty ts)
    (check_periodic_edf_checked_sidecar ts (extracted_periodic_codec ts) cert
      sidecar)

check_periodic_edf_checked_sidecar_extracted_with_offsets :: (List
                                                             ExtractedPeriodicTask)
                                                             ->
                                                             (EDFInfiniteCert
                                                             JobId) ->
                                                             PeriodicEDFCheckedSidecarCert
                                                             -> Bool
check_periodic_edf_checked_sidecar_extracted_with_offsets ts cert sidecar =
  andb (extracted_taskset_nonempty ts)
    (check_periodic_edf_checked_sidecar_with_jobs ts
      (extracted_periodic_offsets ts) (extracted_offset_periodic_jobs ts)
      (extracted_offset_periodic_codec ts) cert sidecar)
