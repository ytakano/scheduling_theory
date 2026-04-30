module JitteredPeriodicEDFSchedulability where

import qualified Prelude

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

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

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 = (\n m -> Prelude.max 0 (n Prelude.- m))

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb n m =
  (Prelude.<=) (Prelude.succ n) m

divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
          Prelude.Integer -> Prod Prelude.Integer Prelude.Integer
divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Pair q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> divmod x' y (Prelude.succ q) y)
      (\u' -> divmod x' y q u')
      u)
    x

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo = (\n m -> if m Prelude.== 0 then n else Prelude.mod n m)

gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> b)
    (\a' -> gcd (modulo b (Prelude.succ a')) (Prelude.succ a'))
    a

lcm :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm a b =
  (Prelude.*) a (div b (gcd a b))

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a l0 -> Cons (f a) (map f l0)}

seq :: Prelude.Integer -> Prelude.Integer -> List Prelude.Integer
seq start len =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Nil)
    (\len0 -> Cons start (seq (Prelude.succ start) len0))
    len

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

concat :: (List (List a1)) -> List a1
concat l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app x (concat l0)}

flat_map :: (a1 -> List a2) -> (List a1) -> List a2
flat_map f l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app (f x) (flat_map f l0)}

forallb :: (a1 -> Prelude.Bool) -> (List a1) -> Prelude.Bool
forallb f l =
  case l of {
   Nil -> Prelude.True;
   Cons a l0 -> (Prelude.&&) (f a) (forallb f l0)}

filter :: (a1 -> Prelude.Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     Prelude.True -> Cons x (filter f l0);
     Prelude.False -> filter f l0}}

find :: (a1 -> Prelude.Bool) -> (List a1) -> Option a1
find f l =
  case l of {
   Nil -> None;
   Cons x tl ->
    case f x of {
     Prelude.True -> Some x;
     Prelude.False -> find f tl}}

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x -> succ (of_succ_nat x))
    n

succ0 :: Prelude.Integer -> Prelude.Integer
succ0 x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ0 p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ0 p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\q -> (\x -> 2 Prelude.* x) (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ0 q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ0 p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ0 p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ0 q))
      (\q -> (\x -> 2 Prelude.* x) (succ0 q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add y ((\x -> 2 Prelude.* x) (mul p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul p y))
    (\_ -> y)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 = (\n m -> if n Prelude.== m then Eq else if n Prelude.< m then Lt else Gt)

type TaskId = Prelude.Integer

type Time = Prelude.Integer

data Task =
   MkTask Prelude.Integer Prelude.Integer Prelude.Integer

task_cost :: Task -> Prelude.Integer
task_cost t =
  case t of {
   MkTask task_cost0 _ _ -> task_cost0}

task_period :: Task -> Prelude.Integer
task_period t =
  case t of {
   MkTask _ task_period0 _ -> task_period0}

task_relative_deadline :: Task -> Prelude.Integer
task_relative_deadline t =
  case t of {
   MkTask _ _ task_relative_deadline0 -> task_relative_deadline0}

expected_release :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                    Prelude.Integer -> Time
expected_release tasks offset _UU03c4_ k =
  (Prelude.+) (offset _UU03c4_)
    ((Prelude.*) k (task_period (tasks _UU03c4_)))

expected_abs_deadline :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                         Prelude.Integer -> Time
expected_abs_deadline tasks offset _UU03c4_ k =
  (Prelude.+) (expected_release tasks offset _UU03c4_ k)
    (task_relative_deadline (tasks _UU03c4_))

bounded_time_points :: Time -> List Time
bounded_time_points h =
  seq 0 (Prelude.succ h)

task_deadline_points_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                             -> Time -> List Time
task_deadline_points_upto tasks offset _UU03c4_ h =
  filter (\t -> (Prelude.<=) t h)
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
      (filter (\t2 -> (Prelude.&&) ((Prelude.<=) t1 t2) ((Prelude.<=) t2 h))
        points))
    points

periodic_hyperperiod :: (TaskId -> Task) -> (List TaskId) -> Time
periodic_hyperperiod tasks enumT =
  case enumT of {
   Nil -> Prelude.succ 0;
   Cons _UU03c4_ enumT' ->
    lcm (task_period (tasks _UU03c4_)) (periodic_hyperperiod tasks enumT')}

periodic_max_relative_deadline :: (TaskId -> Task) -> (List TaskId) -> Time
periodic_max_relative_deadline tasks enumT =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    Prelude.max (task_relative_deadline (tasks _UU03c4_))
      (periodic_max_relative_deadline tasks enumT')}

jittered_index_may_be_in_window_b :: (TaskId -> Task) -> (TaskId -> Time) ->
                                     (TaskId -> Time) -> TaskId -> Time ->
                                     Time -> Prelude.Integer -> Prelude.Bool
jittered_index_may_be_in_window_b tasks offset jitter _UU03c4_ t1 t2 k =
  (Prelude.&&) ((Prelude.<=) (task_relative_deadline (tasks _UU03c4_)) t2)
    ((Prelude.<=) (Prelude.max t1 (expected_release tasks offset _UU03c4_ k))
      (Prelude.min (sub t2 (task_relative_deadline (tasks _UU03c4_)))
        ((Prelude.+) (expected_release tasks offset _UU03c4_ k)
          (jitter _UU03c4_))))

jittered_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (TaskId -> Time) -> TaskId -> Time -> Time ->
                                Prelude.Integer
jittered_periodic_dbf_window tasks offset jitter _UU03c4_ t1 t2 =
  (Prelude.*)
    (length
      (filter
        (jittered_index_may_be_in_window_b tasks offset jitter _UU03c4_ t1
          t2)
        (seq 0 (Prelude.succ t2))))
    (task_cost (tasks _UU03c4_))

taskset_jittered_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> (List 
                                        TaskId) -> Time -> Time ->
                                        Prelude.Integer
taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1 t2 =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    (Prelude.+)
      (jittered_periodic_dbf_window tasks offset jitter _UU03c4_ t1 t2)
      (taskset_jittered_periodic_dbf_window tasks offset jitter enumT' t1 t2)}

nat_interval_count :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
nat_interval_count lo hi =
  case (Prelude.<=) lo hi of {
   Prelude.True -> Prelude.succ (sub hi lo);
   Prelude.False -> 0}

ceil_div_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ceil_div_pos n p =
  div (sub ((Prelude.+) n p) (Prelude.succ 0)) p

ap_first_index_at_or_after :: Prelude.Integer -> Prelude.Integer ->
                              Prelude.Integer -> Prelude.Integer
ap_first_index_at_or_after start period lo =
  case (Prelude.<=) lo start of {
   Prelude.True -> 0;
   Prelude.False -> ceil_div_pos (sub lo start) period}

ap_index_count :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer ->
                  Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ap_index_count start period lo hi limit =
  case (Prelude.==) period 0 of {
   Prelude.True ->
    case (Prelude.&&) ((Prelude.<=) lo start) ((Prelude.<=) start hi) of {
     Prelude.True -> Prelude.succ limit;
     Prelude.False -> 0};
   Prelude.False ->
    case (Prelude.<=) start hi of {
     Prelude.True ->
      let {first = ap_first_index_at_or_after start period lo} in
      let {last = Prelude.min limit (div (sub hi start) period)} in
      nat_interval_count first last;
     Prelude.False -> 0}}

jittered_periodic_fast_release_count :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> TaskId -> Time
                                        -> Time -> Prelude.Integer
jittered_periodic_fast_release_count tasks offset jitter _UU03c4_ t1 t2 =
  let {d = task_relative_deadline (tasks _UU03c4_)} in
  case (Prelude.&&) ((Prelude.<=) d t2) ((Prelude.<=) t1 (sub t2 d)) of {
   Prelude.True ->
    ap_index_count (offset _UU03c4_) (task_period (tasks _UU03c4_))
      (sub t1 (jitter _UU03c4_)) (sub t2 d) t2;
   Prelude.False -> 0}

jittered_periodic_fast_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) ->
                                     (TaskId -> Time) -> TaskId -> Time ->
                                     Time -> Prelude.Integer
jittered_periodic_fast_dbf_window tasks offset jitter _UU03c4_ t1 t2 =
  (Prelude.*)
    (jittered_periodic_fast_release_count tasks offset jitter _UU03c4_ t1 t2)
    (task_cost (tasks _UU03c4_))

taskset_jittered_periodic_fast_dbf_window :: (TaskId -> Task) -> (TaskId ->
                                             Time) -> (TaskId -> Time) ->
                                             (List TaskId) -> Time -> Time ->
                                             Prelude.Integer
taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT t1 t2 =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    (Prelude.+)
      (jittered_periodic_fast_dbf_window tasks offset jitter _UU03c4_ t1 t2)
      (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT'
        t1 t2)}

type JitteredCompactDbfBasis = List (Prod Time (List Time))

data TimeRange =
   MkTimeRange Time Time

time_range_start :: TimeRange -> Time
time_range_start t =
  case t of {
   MkTimeRange time_range_start0 _ -> time_range_start0}

time_range_end :: TimeRange -> Time
time_range_end t =
  case t of {
   MkTimeRange _ time_range_end0 -> time_range_end0}

time_range_wf_b :: TimeRange -> Prelude.Bool
time_range_wf_b r =
  ltb (time_range_start r) (time_range_end r)

time_ranges_cover_from_b :: Time -> (List TimeRange) -> Time -> Prelude.Bool
time_ranges_cover_from_b expected_start ranges limit =
  case ranges of {
   Nil -> (Prelude.==) expected_start limit;
   Cons r ranges' ->
    (Prelude.&&)
      ((Prelude.&&) ((Prelude.==) expected_start (time_range_start r))
        (time_range_wf_b r))
      (time_ranges_cover_from_b (time_range_end r) ranges' limit)}

time_ranges_cover_horizon_b :: Time -> (List TimeRange) -> Prelude.Bool
time_ranges_cover_horizon_b h ranges =
  time_ranges_cover_from_b 0 ranges (Prelude.succ h)

jittered_compact_basis_row_windows :: (Prod Time (List Time)) -> List
                                      (Prod Time Time)
jittered_compact_basis_row_windows row =
  case row of {
   Pair t2 left_edges -> map (\t1 -> Pair t1 t2) left_edges}

jittered_compact_basis_block_windows :: JitteredCompactDbfBasis -> List
                                        (Prod Time Time)
jittered_compact_basis_block_windows block =
  concat (map jittered_compact_basis_row_windows block)

jittered_compact_basis_windows :: JitteredCompactDbfBasis -> List
                                  (Prod Time Time)
jittered_compact_basis_windows basis =
  flat_map (\row ->
    case row of {
     Pair t2 left_edges -> map (\t1 -> Pair t1 t2) left_edges}) basis

jittered_reduced_left_edge_b :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (TaskId -> Time) -> (List TaskId) -> Time ->
                                Time -> Prelude.Bool
jittered_reduced_left_edge_b tasks offset jitter enumT t2 t1 =
  (Prelude.||) ((Prelude.==) t1 t2)
    (Prelude.not
      ((Prelude.==)
        (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT
          t1 t2)
        (taskset_jittered_periodic_fast_dbf_window tasks offset jitter enumT
          (Prelude.succ t1) t2)))

jittered_reduced_left_edges_for_t2 :: (TaskId -> Task) -> (TaskId -> Time) ->
                                      (TaskId -> Time) -> (List TaskId) ->
                                      Time -> List Time
jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2 =
  filter (jittered_reduced_left_edge_b tasks offset jitter enumT t2)
    (bounded_time_points t2)

jittered_reduced_compact_basis_row :: (TaskId -> Task) -> (TaskId -> Time) ->
                                      (TaskId -> Time) -> (List TaskId) ->
                                      Time -> Prod Time (List Time)
jittered_reduced_compact_basis_row tasks offset jitter enumT t2 =
  Pair t2 (jittered_reduced_left_edges_for_t2 tasks offset jitter enumT t2)

jittered_reduced_compact_basis_range :: (TaskId -> Task) -> (TaskId -> Time)
                                        -> (TaskId -> Time) -> (List
                                        TaskId) -> Time -> Time ->
                                        JitteredCompactDbfBasis
jittered_reduced_compact_basis_range tasks offset jitter enumT lo hi =
  map (jittered_reduced_compact_basis_row tasks offset jitter enumT)
    (seq lo (sub hi lo))

jittered_reduced_compact_basis_upto :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (TaskId -> Time) -> (List TaskId)
                                       -> Time -> JitteredCompactDbfBasis
jittered_reduced_compact_basis_upto tasks offset jitter enumT h =
  jittered_reduced_compact_basis_range tasks offset jitter enumT 0
    (Prelude.succ h)

data JitteredEDFCompactDbfCertificate =
   Build_JitteredEDFCompactDbfCertificate Time JitteredCompactDbfBasis 
 Prelude.Bool

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

jedf_all_basis_checked :: JitteredEDFCompactDbfCertificate -> Prelude.Bool
jedf_all_basis_checked j =
  case j of {
   Build_JitteredEDFCompactDbfCertificate _ _ jedf_all_basis_checked0 ->
    jedf_all_basis_checked0}

time_list_eqb :: (List Time) -> (List Time) -> Prelude.Bool
time_list_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> Prelude.True;
           Cons _ _ -> Prelude.False};
   Cons x xs' ->
    case ys of {
     Nil -> Prelude.False;
     Cons y ys' -> (Prelude.&&) ((Prelude.==) x y) (time_list_eqb xs' ys')}}

compact_dbf_basis_row_eqb :: (Prod Time (List Time)) -> (Prod Time
                             (List Time)) -> Prelude.Bool
compact_dbf_basis_row_eqb r1 r2 =
  case r1 of {
   Pair t2_1 left_edges1 ->
    case r2 of {
     Pair t2_2 left_edges2 ->
      (Prelude.&&) ((Prelude.==) t2_1 t2_2)
        (time_list_eqb left_edges1 left_edges2)}}

compact_dbf_basis_eqb :: JitteredCompactDbfBasis -> JitteredCompactDbfBasis
                         -> Prelude.Bool
compact_dbf_basis_eqb xs ys =
  case xs of {
   Nil -> case ys of {
           Nil -> Prelude.True;
           Cons _ _ -> Prelude.False};
   Cons x xs' ->
    case ys of {
     Nil -> Prelude.False;
     Cons y ys' ->
      (Prelude.&&) (compact_dbf_basis_row_eqb x y)
        (compact_dbf_basis_eqb xs' ys')}}

compact_dbf_basis_ranges_eqb :: (List JitteredCompactDbfBasis) -> (List
                                JitteredCompactDbfBasis) -> Prelude.Bool
compact_dbf_basis_ranges_eqb actual_ranges expected_ranges =
  case actual_ranges of {
   Nil ->
    case expected_ranges of {
     Nil -> Prelude.True;
     Cons _ _ -> Prelude.False};
   Cons actual_range actual_ranges' ->
    case expected_ranges of {
     Nil -> Prelude.False;
     Cons expected_range expected_ranges' ->
      (Prelude.&&) (compact_dbf_basis_eqb actual_range expected_range)
        (compact_dbf_basis_ranges_eqb actual_ranges' expected_ranges')}}

compact_dbf_basis_blocks_eqb :: (List JitteredCompactDbfBasis) -> (List
                                JitteredCompactDbfBasis) -> Prelude.Bool
compact_dbf_basis_blocks_eqb actual_blocks expected_blocks =
  compact_dbf_basis_eqb (concat actual_blocks) (concat expected_blocks)

check_jittered_edf_compact_dbf_certificate_block_basis :: (List
                                                          JitteredCompactDbfBasis)
                                                          -> (List
                                                          JitteredCompactDbfBasis)
                                                          ->
                                                          JitteredEDFCompactDbfCertificate
                                                          -> Prelude.Bool
check_jittered_edf_compact_dbf_certificate_block_basis actual_blocks expected_blocks cert =
  (Prelude.&&)
    (compact_dbf_basis_eqb (jedf_compact_basis cert) (concat actual_blocks))
    (compact_dbf_basis_blocks_eqb actual_blocks expected_blocks)

check_jittered_edf_compact_dbf_certificate_block_basis_for_expected :: 
  JitteredCompactDbfBasis -> (List JitteredCompactDbfBasis) -> (List
  JitteredCompactDbfBasis) -> JitteredEDFCompactDbfCertificate ->
  Prelude.Bool
check_jittered_edf_compact_dbf_certificate_block_basis_for_expected expected_basis actual_blocks expected_blocks cert =
  (Prelude.&&)
    (compact_dbf_basis_eqb expected_basis (concat expected_blocks))
    (check_jittered_edf_compact_dbf_certificate_block_basis actual_blocks
      expected_blocks cert)

check_jittered_edf_compact_dbf_certificate_fields :: Time ->
                                                     JitteredCompactDbfBasis
                                                     ->
                                                     JitteredEDFCompactDbfCertificate
                                                     -> Prelude.Bool
check_jittered_edf_compact_dbf_certificate_fields expected_cutoff expected_basis cert =
  (Prelude.&&)
    ((Prelude.&&) ((Prelude.==) (jedf_compact_cutoff cert) expected_cutoff)
      (compact_dbf_basis_eqb (jedf_compact_basis cert) expected_basis))
    (jedf_all_basis_checked cert)

check_jittered_edf_compact_dbf_certificate_header :: Time ->
                                                     JitteredEDFCompactDbfCertificate
                                                     -> Prelude.Bool
check_jittered_edf_compact_dbf_certificate_header expected_cutoff cert =
  (Prelude.&&) ((Prelude.==) (jedf_compact_cutoff cert) expected_cutoff)
    (jedf_all_basis_checked cert)

first_jittered_window_dbf_overload_upto :: (TaskId -> Task) -> (TaskId ->
                                           Time) -> (TaskId -> Time) -> (List
                                           TaskId) -> Time -> Option
                                           (Prod Time Time)
first_jittered_window_dbf_overload_upto tasks offset jitter enumT h =
  find (\w ->
    case w of {
     Pair t1 t2 ->
      Prelude.not
        ((Prelude.<=)
          (taskset_jittered_periodic_dbf_window tasks offset jitter enumT t1
            t2)
          (sub t2 t1))})
    (critical_dbf_windows_upto tasks offset enumT h)

data ExtractedPeriodicTask =
   MkExtractedPeriodicTask Prelude.Integer Prelude.Integer Prelude.Integer 
 Prelude.Integer

extracted_task_cost :: ExtractedPeriodicTask -> Prelude.Integer
extracted_task_cost e =
  case e of {
   MkExtractedPeriodicTask extracted_task_cost0 _ _ _ -> extracted_task_cost0}

extracted_task_period :: ExtractedPeriodicTask -> Prelude.Integer
extracted_task_period e =
  case e of {
   MkExtractedPeriodicTask _ extracted_task_period0 _ _ ->
    extracted_task_period0}

extracted_task_relative_deadline :: ExtractedPeriodicTask -> Prelude.Integer
extracted_task_relative_deadline e =
  case e of {
   MkExtractedPeriodicTask _ _ extracted_task_relative_deadline0 _ ->
    extracted_task_relative_deadline0}

extracted_task_offset :: ExtractedPeriodicTask -> Prelude.Integer
extracted_task_offset e =
  case e of {
   MkExtractedPeriodicTask _ _ _ extracted_task_offset0 ->
    extracted_task_offset0}

data ExtractedJitteredPeriodicTask =
   MkExtractedJitteredPeriodicTask Prelude.Integer Prelude.Integer Prelude.Integer 
 Prelude.Integer Prelude.Integer

ejp_cost :: ExtractedJitteredPeriodicTask -> Prelude.Integer
ejp_cost e =
  case e of {
   MkExtractedJitteredPeriodicTask ejp_cost0 _ _ _ _ -> ejp_cost0}

ejp_period :: ExtractedJitteredPeriodicTask -> Prelude.Integer
ejp_period e =
  case e of {
   MkExtractedJitteredPeriodicTask _ ejp_period0 _ _ _ -> ejp_period0}

ejp_relative_deadline :: ExtractedJitteredPeriodicTask -> Prelude.Integer
ejp_relative_deadline e =
  case e of {
   MkExtractedJitteredPeriodicTask _ _ ejp_relative_deadline0 _ _ ->
    ejp_relative_deadline0}

ejp_offset :: ExtractedJitteredPeriodicTask -> Prelude.Integer
ejp_offset e =
  case e of {
   MkExtractedJitteredPeriodicTask _ _ _ ejp_offset0 _ -> ejp_offset0}

ejp_release_jitter :: ExtractedJitteredPeriodicTask -> Prelude.Integer
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
  MkExtractedJitteredPeriodicTask (Prelude.succ 0) (Prelude.succ 0)
    (Prelude.succ 0) 0 0

extracted_periodic_as_jittered_zero_jitter :: ExtractedPeriodicTask ->
                                              ExtractedJitteredPeriodicTask
extracted_periodic_as_jittered_zero_jitter _UU03c4_ =
  MkExtractedJitteredPeriodicTask (extracted_task_cost _UU03c4_)
    (extracted_task_period _UU03c4_)
    (extracted_task_relative_deadline _UU03c4_)
    (extracted_task_offset _UU03c4_) 0

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
  seq 0 (length ts)

extracted_jittered_task_wf :: ExtractedJitteredPeriodicTask -> Prelude.Bool
extracted_jittered_task_wf _UU03c4_ =
  (Prelude.&&)
    ((Prelude.&&) (ltb 0 (ejp_cost _UU03c4_)) (ltb 0 (ejp_period _UU03c4_)))
    (ltb 0 (ejp_relative_deadline _UU03c4_))

extracted_jittered_taskset_wf :: (List ExtractedJitteredPeriodicTask) ->
                                 Prelude.Bool
extracted_jittered_taskset_wf ts =
  forallb extracted_jittered_task_wf ts

jittered_window_capacity_N :: Time -> Time -> Prelude.Integer
jittered_window_capacity_N t1 t2 =
  (\x -> x) (sub t2 t1)

jittered_periodic_fast_release_count_N :: (TaskId -> Task) -> (TaskId ->
                                          Time) -> (TaskId -> Time) -> TaskId
                                          -> Time -> Time -> Prelude.Integer
jittered_periodic_fast_release_count_N tasks offset jitter _UU03c4_ t1 t2 =
  (\x -> x)
    (jittered_periodic_fast_release_count tasks offset jitter _UU03c4_ t1 t2)

jittered_periodic_fast_dbf_window_N :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (TaskId -> Time) -> TaskId -> Time
                                       -> Time -> Prelude.Integer
jittered_periodic_fast_dbf_window_N tasks offset jitter _UU03c4_ t1 t2 =
  (Prelude.*)
    (jittered_periodic_fast_release_count_N tasks offset jitter _UU03c4_ t1
      t2)
    ((\x -> x) (task_cost (tasks _UU03c4_)))

taskset_jittered_periodic_fast_dbf_window_N :: (TaskId -> Task) -> (TaskId ->
                                               Time) -> (TaskId -> Time) ->
                                               (List TaskId) -> Time -> Time
                                               -> Prelude.Integer
taskset_jittered_periodic_fast_dbf_window_N tasks offset jitter enumT t1 t2 =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    (Prelude.+)
      (jittered_periodic_fast_dbf_window_N tasks offset jitter _UU03c4_ t1
        t2)
      (taskset_jittered_periodic_fast_dbf_window_N tasks offset jitter enumT'
        t1 t2)}

jittered_periodic_fast_dbf_window_ok_N_b :: (TaskId -> Task) -> (TaskId ->
                                            Time) -> (TaskId -> Time) ->
                                            (List TaskId) -> Time -> Time ->
                                            Prelude.Bool
jittered_periodic_fast_dbf_window_ok_N_b tasks offset jitter enumT t1 t2 =
  (Prelude.<=)
    (taskset_jittered_periodic_fast_dbf_window_N tasks offset jitter enumT t1
      t2)
    (jittered_window_capacity_N t1 t2)

jittered_window_fast_ndbf_test_upto :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (TaskId -> Time) -> (List TaskId)
                                       -> Time -> Prelude.Bool
jittered_window_fast_ndbf_test_upto tasks offset jitter enumT h =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      jittered_periodic_fast_dbf_window_ok_N_b tasks offset jitter enumT t1
        t2})
    (critical_dbf_windows_upto tasks offset enumT h)

periodic_max_offset :: (TaskId -> Time) -> (List TaskId) -> Time
periodic_max_offset offset enumT =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    Prelude.max (offset _UU03c4_) (periodic_max_offset offset enumT')}

offset_window_dbf_cutoff_bound :: (TaskId -> Task) -> (TaskId -> Time) ->
                                  (List TaskId) -> Time
offset_window_dbf_cutoff_bound tasks offset enumT =
  let {
   horizon_base = (Prelude.+)
                    ((Prelude.+) (periodic_max_offset offset enumT)
                      (periodic_max_relative_deadline tasks enumT))
                    (periodic_hyperperiod tasks enumT)}
  in
  (Prelude.+) horizon_base
    ((Prelude.*) (Prelude.succ horizon_base)
      (periodic_hyperperiod tasks enumT))

jittered_max_release_jitter :: (TaskId -> Time) -> (List TaskId) -> Time
jittered_max_release_jitter jitter enumT =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    Prelude.max (jitter _UU03c4_) (jittered_max_release_jitter jitter enumT')}

jittered_offset_window_dbf_cutoff_bound :: (TaskId -> Task) -> (TaskId ->
                                           Time) -> (TaskId -> Time) -> (List
                                           TaskId) -> Time
jittered_offset_window_dbf_cutoff_bound tasks offset jitter enumT =
  (Prelude.+) (offset_window_dbf_cutoff_bound tasks offset enumT)
    (jittered_max_release_jitter jitter enumT)

extracted_jittered_offset_window_dbf_cutoff_bound :: (List
                                                     ExtractedJitteredPeriodicTask)
                                                     -> Time
extracted_jittered_offset_window_dbf_cutoff_bound ts =
  jittered_offset_window_dbf_cutoff_bound
    (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)

extracted_jittered_offset_window_ndbf_test_by_cutoff :: (List
                                                        ExtractedJitteredPeriodicTask)
                                                        -> Prelude.Bool
extracted_jittered_offset_window_ndbf_test_by_cutoff ts =
  jittered_window_fast_ndbf_test_upto (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts)
    (extracted_jittered_offset_window_dbf_cutoff_bound ts)

extracted_jittered_offset_window_dbf_test_by_cutoff :: (List
                                                       ExtractedJitteredPeriodicTask)
                                                       -> Prelude.Bool
extracted_jittered_offset_window_dbf_test_by_cutoff =
  extracted_jittered_offset_window_ndbf_test_by_cutoff

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
                                                         -> Prelude.Bool
extracted_jittered_offset_window_dbf_decide_by_cutoff ts =
  (Prelude.&&) (extracted_jittered_taskset_wf ts)
    (extracted_jittered_offset_window_dbf_test_by_cutoff ts)

jittered_periodic_offset_window_schedulability_cutoff_bound :: (List
                                                               ExtractedJitteredPeriodicTask)
                                                               -> Time
jittered_periodic_offset_window_schedulability_cutoff_bound =
  extracted_jittered_offset_window_dbf_cutoff_bound

jittered_periodic_offset_window_schedulability_decide :: (List
                                                         ExtractedJitteredPeriodicTask)
                                                         -> Prelude.Bool
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

jittered_edf_compact_dbf_certificate_expected_basis_range :: (List
                                                             ExtractedJitteredPeriodicTask)
                                                             -> Time -> Time
                                                             ->
                                                             JitteredCompactDbfBasis
jittered_edf_compact_dbf_certificate_expected_basis_range ts lo hi =
  jittered_reduced_compact_basis_range (jittered_tasks_of_extracted_list ts)
    (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
    (jittered_enumT_of_extracted_list ts) lo hi

jittered_edf_compact_dbf_certificate_expected_basis_ranges :: (List
                                                              ExtractedJitteredPeriodicTask)
                                                              -> (List
                                                              TimeRange) ->
                                                              List
                                                              JitteredCompactDbfBasis
jittered_edf_compact_dbf_certificate_expected_basis_ranges ts ranges =
  map (\r ->
    jittered_edf_compact_dbf_certificate_expected_basis_range ts
      (time_range_start r) (time_range_end r))
    ranges

jittered_fast_compact_basis_ndbf_test :: (TaskId -> Task) -> (TaskId -> Time)
                                         -> (TaskId -> Time) -> (List 
                                         TaskId) -> JitteredCompactDbfBasis
                                         -> Prelude.Bool
jittered_fast_compact_basis_ndbf_test tasks offset jitter enumT basis =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      (Prelude.&&) ((Prelude.<=) t1 t2)
        (jittered_periodic_fast_dbf_window_ok_N_b tasks offset jitter enumT
          t1 t2)})
    (jittered_compact_basis_windows basis)

jittered_fast_compact_basis_ndbf_block_test :: (TaskId -> Task) -> (TaskId ->
                                               Time) -> (TaskId -> Time) ->
                                               (List TaskId) ->
                                               JitteredCompactDbfBasis ->
                                               Prelude.Bool
jittered_fast_compact_basis_ndbf_block_test tasks offset jitter enumT block =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      (Prelude.&&) ((Prelude.<=) t1 t2)
        (jittered_periodic_fast_dbf_window_ok_N_b tasks offset jitter enumT
          t1 t2)})
    (jittered_compact_basis_block_windows block)

jittered_fast_compact_basis_ndbf_blocks_test :: (TaskId -> Task) -> (TaskId
                                                -> Time) -> (TaskId -> Time)
                                                -> (List TaskId) -> (List
                                                JitteredCompactDbfBasis) ->
                                                Prelude.Bool
jittered_fast_compact_basis_ndbf_blocks_test tasks offset jitter enumT blocks =
  forallb
    (jittered_fast_compact_basis_ndbf_block_test tasks offset jitter enumT)
    blocks

check_jittered_edf_compact_dbf_certificate_extracted :: (List
                                                        ExtractedJitteredPeriodicTask)
                                                        ->
                                                        JitteredEDFCompactDbfCertificate
                                                        -> Prelude.Bool
check_jittered_edf_compact_dbf_certificate_extracted ts cert =
  (Prelude.&&)
    ((Prelude.&&) (extracted_jittered_taskset_wf ts)
      (check_jittered_edf_compact_dbf_certificate_fields
        (jittered_edf_compact_dbf_certificate_expected_cutoff ts)
        (jittered_edf_compact_dbf_certificate_expected_basis ts) cert))
    (jittered_fast_compact_basis_ndbf_test
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts) (jedf_compact_basis cert))

check_jittered_edf_compact_dbf_certificate_header_extracted :: (List
                                                               ExtractedJitteredPeriodicTask)
                                                               ->
                                                               JitteredEDFCompactDbfCertificate
                                                               ->
                                                               Prelude.Bool
check_jittered_edf_compact_dbf_certificate_header_extracted ts cert =
  (Prelude.&&) (extracted_jittered_taskset_wf ts)
    (check_jittered_edf_compact_dbf_certificate_header
      (jittered_edf_compact_dbf_certificate_expected_cutoff ts) cert)

check_jittered_edf_compact_dbf_certificate_blocks_extracted :: (List
                                                               ExtractedJitteredPeriodicTask)
                                                               -> (List
                                                               JitteredCompactDbfBasis)
                                                               -> (List
                                                               JitteredCompactDbfBasis)
                                                               ->
                                                               JitteredEDFCompactDbfCertificate
                                                               ->
                                                               Prelude.Bool
check_jittered_edf_compact_dbf_certificate_blocks_extracted ts actual_blocks expected_blocks cert =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) (extracted_jittered_taskset_wf ts)
        (check_jittered_edf_compact_dbf_certificate_header
          (jittered_edf_compact_dbf_certificate_expected_cutoff ts) cert))
      (check_jittered_edf_compact_dbf_certificate_block_basis_for_expected
        (jittered_edf_compact_dbf_certificate_expected_basis ts)
        actual_blocks expected_blocks cert))
    (jittered_fast_compact_basis_ndbf_blocks_test
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts) actual_blocks)

check_jittered_edf_compact_dbf_certificate_range_extracted :: (List
                                                              ExtractedJitteredPeriodicTask)
                                                              -> Time -> Time
                                                              ->
                                                              JitteredCompactDbfBasis
                                                              -> Prelude.Bool
check_jittered_edf_compact_dbf_certificate_range_extracted ts lo hi actual_range =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) (extracted_jittered_taskset_wf ts)
        (time_range_wf_b (MkTimeRange lo hi)))
      (compact_dbf_basis_eqb actual_range
        (jittered_edf_compact_dbf_certificate_expected_basis_range ts lo hi)))
    (jittered_fast_compact_basis_ndbf_block_test
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts) actual_range)

check_jittered_edf_compact_dbf_certificate_ranges_extracted :: (List
                                                               ExtractedJitteredPeriodicTask)
                                                               -> (List
                                                               TimeRange) ->
                                                               (List
                                                               JitteredCompactDbfBasis)
                                                               ->
                                                               JitteredEDFCompactDbfCertificate
                                                               ->
                                                               Prelude.Bool
check_jittered_edf_compact_dbf_certificate_ranges_extracted ts ranges actual_ranges cert =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) (extracted_jittered_taskset_wf ts)
            (check_jittered_edf_compact_dbf_certificate_header
              (jittered_edf_compact_dbf_certificate_expected_cutoff ts) cert))
          (time_ranges_cover_horizon_b
            (jittered_edf_compact_dbf_certificate_expected_cutoff ts) ranges))
        (compact_dbf_basis_eqb (jedf_compact_basis cert)
          (concat actual_ranges)))
      (compact_dbf_basis_ranges_eqb actual_ranges
        (jittered_edf_compact_dbf_certificate_expected_basis_ranges ts
          ranges)))
    (jittered_fast_compact_basis_ndbf_blocks_test
      (jittered_tasks_of_extracted_list ts)
      (jittered_offset_of_extracted_list ts) (jitter_of_extracted_list ts)
      (jittered_enumT_of_extracted_list ts) actual_ranges)
