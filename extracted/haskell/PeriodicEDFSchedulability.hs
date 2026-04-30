module PeriodicEDFSchedulability where

import qualified Prelude

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

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

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

flat_map :: (a1 -> List a2) -> (List a1) -> List a2
flat_map f l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app (f x) (flat_map f l0)}

existsb :: (a1 -> Prelude.Bool) -> (List a1) -> Prelude.Bool
existsb f l =
  case l of {
   Nil -> Prelude.False;
   Cons a l0 -> (Prelude.||) (f a) (existsb f l0)}

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

combine :: (List a1) -> (List a2) -> List (Prod a1 a2)
combine l l' =
  case l of {
   Nil -> Nil;
   Cons x tl ->
    case l' of {
     Nil -> Nil;
     Cons y tl' -> Cons (Pair x y) (combine tl tl')}}

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

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x) (pred_double p)))
    (\_ -> IsNul)
    x

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask p q))
      (\q -> succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> IsNeg)
      (\_ -> IsNeg)
      (\_ -> IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask_carry p q))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\_ -> double_pred_mask p)
      y)
    (\_ -> IsNeg)
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

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

double :: Prelude.Integer -> Prelude.Integer
double n =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    n

sub1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub1 = (\n m -> Prelude.max 0 (n Prelude.- m))

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 = (\n m -> if n Prelude.== m then Eq else if n Prelude.< m then Lt else Gt)

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case (Prelude.<=) b r' of {
       Prelude.True -> Pair (succ_double q) (sub1 r' b);
       Prelude.False -> Pair (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case (Prelude.<=) b r' of {
       Prelude.True -> Pair (succ_double q) (sub1 r' b);
       Prelude.False -> Pair (double q) r'}})
    (\_ ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ -> Pair 0 ((\x -> x) 1))
      (\p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\_ -> Pair 0 ((\x -> x) 1))
        (\_ -> Pair 0 ((\x -> x) 1))
        (\_ -> Pair ((\x -> x) 1) 0)
        p)
      b)
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ -> Pair 0 0)
    (\na ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ -> Pair 0 a)
      (\_ -> pos_div_eucl na b)
      b)
    a

div0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div0 = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

compare1 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare1 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

of_nat :: Prelude.Integer -> Prelude.Integer
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 -> (\x -> x) (of_succ_nat n0))
    n

type JobId = Prelude.Integer

type TaskId = Prelude.Integer

type CPU = Prelude.Integer

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

data EDFPrefixCert job =
   Build_EDFPrefixCert Time (List job) (List (Option job)) (List Time) 
 (List (List Prelude.Bool))

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

prefix_backlog_free_matrix :: (EDFPrefixCert a1) -> List (List Prelude.Bool)
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
 (List Prelude.Integer) (List Prelude.Integer)

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

transport_job_class :: (EDFTransportCert a1) -> List Prelude.Integer
transport_job_class e =
  case e of {
   Build_EDFTransportCert _ _ _ transport_job_class0 _ ->
    transport_job_class0}

transport_job_shift :: (EDFTransportCert a1) -> List Prelude.Integer
transport_job_shift e =
  case e of {
   Build_EDFTransportCert _ _ _ _ transport_job_shift0 ->
    transport_job_shift0}

data EDFDBFCert =
   Build_EDFDBFCert Time (List Prelude.Bool)

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

check_bool_rows_have_length :: Prelude.Integer -> (List (List Prelude.Bool))
                               -> Prelude.Bool
check_bool_rows_have_length n rows =
  forallb (\row -> (Prelude.==) (length row) n) rows

check_nat_entries_below :: Prelude.Integer -> (List Prelude.Integer) ->
                           Prelude.Bool
check_nat_entries_below bound xs =
  forallb (\x -> ltb x bound) xs

check_prefix_cert :: (EDFPrefixCert a1) -> Prelude.Bool
check_prefix_cert c =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.==) (length (prefix_slots c)) (prefix_horizon c))
        ((Prelude.==) (length (prefix_completed_by c))
          (length (prefix_basis_jobs c))))
      ((Prelude.==) (length (prefix_backlog_free_matrix c))
        (length (prefix_basis_jobs c))))
    (check_bool_rows_have_length (length (prefix_basis_jobs c))
      (prefix_backlog_free_matrix c))

check_transport_cert :: (EDFTransportCert a1) -> Prelude.Bool
check_transport_cert c =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) (ltb 0 (transport_period c))
        ((Prelude.==) (length (transport_job_class c))
          (length (transport_basis_jobs c))))
      ((Prelude.==) (length (transport_job_shift c))
        (length (transport_basis_jobs c))))
    (check_nat_entries_below (length (transport_classes c))
      (transport_job_class c))

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

periodic_dbf :: (TaskId -> Task) -> TaskId -> Time -> Prelude.Integer
periodic_dbf tasks _UU03c4_ h =
  case ltb h (task_relative_deadline (tasks _UU03c4_)) of {
   Prelude.True -> 0;
   Prelude.False ->
    (Prelude.*) (Prelude.succ
      (div (sub h (task_relative_deadline (tasks _UU03c4_)))
        (task_period (tasks _UU03c4_))))
      (task_cost (tasks _UU03c4_))}

taskset_periodic_dbf :: (TaskId -> Task) -> (List TaskId) -> Time ->
                        Prelude.Integer
taskset_periodic_dbf tasks enumT h =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    (Prelude.+) (periodic_dbf tasks _UU03c4_ h)
      (taskset_periodic_dbf tasks enumT' h)}

type GenericSchedulingAlgorithm =
  (JobId -> Job) -> Prelude.Integer -> Schedule -> Time -> (List JobId) ->
  Option JobId
  -- singleton inductive, whose constructor was mkGenericSchedulingAlgorithm
  
choose :: GenericSchedulingAlgorithm -> (JobId -> Job) -> Prelude.Integer ->
          Schedule -> Time -> (List JobId) -> Option JobId
choose g =
  g

type CandidateSource =
  (JobId -> Job) -> Prelude.Integer -> Schedule -> Time -> List JobId

enum_candidates_of :: (List JobId) -> CandidateSource
enum_candidates_of enumJ _ _ _ _ =
  enumJ

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

generated_periodic_job :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                          Prelude.Integer -> Job
generated_periodic_job tasks offset _UU03c4_ k =
  MkJob _UU03c4_ k (expected_release tasks offset _UU03c4_ k)
    (task_cost (tasks _UU03c4_))
    (expected_abs_deadline tasks offset _UU03c4_ k) (\_ -> Prelude.False)

type PeriodicCodec =
  TaskId -> Prelude.Integer -> JobId
  -- singleton inductive, whose constructor was mkPeriodicCodec
  
global_periodic_job_id_of :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId
                             -> Job) -> PeriodicCodec -> TaskId ->
                             Prelude.Integer -> JobId
global_periodic_job_id_of _ _ _ p =
  p

task_position_in_enumT :: (List TaskId) -> TaskId -> Prelude.Integer
task_position_in_enumT enumT _UU03c4_ =
  case enumT of {
   Nil -> 0;
   Cons x xs ->
    case (Prelude.==) x _UU03c4_ of {
     Prelude.True -> 0;
     Prelude.False -> Prelude.succ (task_position_in_enumT xs _UU03c4_)}}

encode_job_id_from_enumT :: (List TaskId) -> TaskId -> Prelude.Integer ->
                            JobId
encode_job_id_from_enumT enumT _UU03c4_ k =
  (Prelude.+) (task_position_in_enumT enumT _UU03c4_)
    ((Prelude.*) (length enumT) k)

decode_job_id_from_enumT :: (List TaskId) -> JobId -> Prod Prelude.Integer
                            Prelude.Integer
decode_job_id_from_enumT enumT j =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Pair 0 j)
    (\n0 ->
    let {n = Prelude.succ n0} in Pair (modulo j n) (div j n))
    (length enumT)

canonical_periodic_jobs_from_enumT :: (TaskId -> Task) -> (TaskId -> Time) ->
                                      (List TaskId) -> JobId -> Job
canonical_periodic_jobs_from_enumT tasks offset enumT j =
  case decode_job_id_from_enumT enumT j of {
   Pair pos k ->
    case nth_error enumT pos of {
     Some _UU03c4_ -> generated_periodic_job tasks offset _UU03c4_ k;
     None -> MkJob 0 j 0 (Prelude.succ (task_cost (tasks 0))) 0 (\_ ->
      Prelude.False)}}

periodic_codec_of_enumT :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                           TaskId) -> PeriodicCodec
periodic_codec_of_enumT _ _ =
  encode_job_id_from_enumT

zero_offset_periodic_codec_of_tasks :: (TaskId -> Task) -> (List TaskId) ->
                                       PeriodicCodec
zero_offset_periodic_codec_of_tasks tasks enumT =
  periodic_codec_of_enumT tasks (\_ -> 0) enumT

type PeriodicFiniteHorizonCodec =
  TaskId -> Prelude.Integer -> JobId
  -- singleton inductive, whose constructor was mkPeriodicFiniteHorizonCodec
  
periodic_job_id_of :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId -> Job)
                      -> Time -> PeriodicFiniteHorizonCodec -> TaskId ->
                      Prelude.Integer -> JobId
periodic_job_id_of _ _ _ _ p =
  p

periodic_finite_horizon_codec_of :: (TaskId -> Task) -> (TaskId -> Time) ->
                                    (JobId -> Job) -> Time -> PeriodicCodec
                                    -> PeriodicFiniteHorizonCodec
periodic_finite_horizon_codec_of tasks offset jobs _ codec =
  global_periodic_job_id_of tasks offset jobs codec

enum_periodic_indices_upto :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                              -> Time -> List Prelude.Integer
enum_periodic_indices_upto tasks offset _UU03c4_ h =
  filter (\k -> ltb (expected_release tasks offset _UU03c4_ k) h) (seq 0 h)

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
                            Time -> Time -> Prelude.Integer -> Prelude.Bool
periodic_index_in_window tasks offset _UU03c4_ t1 t2 k =
  (Prelude.&&) ((Prelude.<=) t1 (expected_release tasks offset _UU03c4_ k))
    ((Prelude.<=) (expected_abs_deadline tasks offset _UU03c4_ k) t2)

periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId -> Time
                       -> Time -> Prelude.Integer
periodic_dbf_window tasks offset _UU03c4_ t1 t2 =
  (Prelude.*)
    (length
      (filter (periodic_index_in_window tasks offset _UU03c4_ t1 t2)
        (seq 0 (Prelude.succ t2))))
    (task_cost (tasks _UU03c4_))

taskset_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                               TaskId) -> Time -> Time -> Prelude.Integer
taskset_periodic_dbf_window tasks offset enumT t1 t2 =
  case enumT of {
   Nil -> 0;
   Cons _UU03c4_ enumT' ->
    (Prelude.+) (periodic_dbf_window tasks offset _UU03c4_ t1 t2)
      (taskset_periodic_dbf_window tasks offset enumT' t1 t2)}

generated_schedule_prefix :: GenericSchedulingAlgorithm -> CandidateSource ->
                             (JobId -> Job) -> Time -> Schedule
generated_schedule_prefix alg candidates_of jobs h =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ _ _ -> None)
    (\h' ->
    let {pref = generated_schedule_prefix alg candidates_of jobs h'} in
    (\t c ->
    case ltb t h' of {
     Prelude.True -> pref t c;
     Prelude.False ->
      case (Prelude.==) t h' of {
       Prelude.True ->
        case (Prelude.==) c 0 of {
         Prelude.True ->
          choose alg jobs (Prelude.succ 0) pref h'
            (candidates_of jobs (Prelude.succ 0) pref h');
         Prelude.False -> None};
       Prelude.False -> None}}))
    h

generated_schedule :: GenericSchedulingAlgorithm -> CandidateSource -> (JobId
                      -> Job) -> Schedule
generated_schedule alg candidates_of jobs t c =
  generated_schedule_prefix alg candidates_of jobs (Prelude.succ t) t c

min_metric_job :: (JobId -> Prelude.Integer) -> (List JobId) -> Option JobId
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

choose_min_metric :: (JobId -> Prelude.Integer) -> (JobId -> Job) ->
                     Prelude.Integer -> Schedule -> Time -> (List JobId) ->
                     Option JobId
choose_min_metric metric jobs m sched t candidates =
  min_metric_job metric
    (filter (\j -> eligibleb jobs m sched j t) candidates)

edf_metric :: (JobId -> Job) -> JobId -> Prelude.Integer
edf_metric jobs j =
  of_nat (job_abs_deadline (jobs j))

choose_edf :: (JobId -> Job) -> Prelude.Integer -> Schedule -> Time -> (List
              JobId) -> Option JobId
choose_edf jobs m sched t candidates =
  choose_min_metric (edf_metric jobs) jobs m sched t candidates

edf_generic_spec :: GenericSchedulingAlgorithm
edf_generic_spec =
  choose_edf

periodic_candidates_before :: (TaskId -> Task) -> (TaskId -> Time) -> (JobId
                              -> Job) -> (List TaskId) -> PeriodicCodec ->
                              CandidateSource
periodic_candidates_before tasks offset jobs enumT codec _ _ _ t =
  enum_periodic_jobs_before tasks offset jobs enumT codec (Prelude.succ t)

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

first_dbf_overload_upto :: (TaskId -> Task) -> (List TaskId) -> Time ->
                           Option Time
first_dbf_overload_upto tasks enumT h =
  find (\t ->
    Prelude.not ((Prelude.<=) (taskset_periodic_dbf tasks enumT t) t))
    (critical_dbf_points_upto tasks (\_ -> 0) enumT h)

first_window_dbf_overload_upto :: (TaskId -> Task) -> (TaskId -> Time) ->
                                  (List TaskId) -> Time -> Option
                                  (Prod Time Time)
first_window_dbf_overload_upto tasks offset enumT h =
  find (\w ->
    case w of {
     Pair t1 t2 ->
      Prelude.not
        ((Prelude.<=) (taskset_periodic_dbf_window tasks offset enumT t1 t2)
          (sub t2 t1))})
    (critical_dbf_windows_upto tasks offset enumT h)

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

scalar_dbf_cutoff_bound :: (TaskId -> Task) -> (List TaskId) -> Time
scalar_dbf_cutoff_bound tasks enumT =
  (Prelude.+) (periodic_max_relative_deadline tasks enumT)
    ((Prelude.*) (Prelude.succ (periodic_max_relative_deadline tasks enumT))
      (periodic_hyperperiod tasks enumT))

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

task_of_extracted :: ExtractedPeriodicTask -> Task
task_of_extracted _UU03c4_ =
  MkTask (extracted_task_cost _UU03c4_) (extracted_task_period _UU03c4_)
    (extracted_task_relative_deadline _UU03c4_)

default_extracted_periodic_task :: ExtractedPeriodicTask
default_extracted_periodic_task =
  MkExtractedPeriodicTask (Prelude.succ 0) (Prelude.succ 0) (Prelude.succ 0)
    0

tasks_of_extracted_list :: (List ExtractedPeriodicTask) -> TaskId -> Task
tasks_of_extracted_list ts _UU03c4_ =
  task_of_extracted (nth _UU03c4_ ts default_extracted_periodic_task)

offset_of_extracted_list :: (List ExtractedPeriodicTask) -> TaskId -> Time
offset_of_extracted_list ts _UU03c4_ =
  extracted_task_offset (nth _UU03c4_ ts default_extracted_periodic_task)

enumT_of_extracted_list :: (List ExtractedPeriodicTask) -> List TaskId
enumT_of_extracted_list ts =
  seq 0 (length ts)

extracted_task_wf :: ExtractedPeriodicTask -> Prelude.Bool
extracted_task_wf _UU03c4_ =
  (Prelude.&&)
    ((Prelude.&&) (ltb 0 (extracted_task_cost _UU03c4_))
      (ltb 0 (extracted_task_period _UU03c4_)))
    (ltb 0 (extracted_task_relative_deadline _UU03c4_))

extracted_taskset_wf :: (List ExtractedPeriodicTask) -> Prelude.Bool
extracted_taskset_wf ts =
  forallb extracted_task_wf ts

n_expected_release :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                      Prelude.Integer -> Prelude.Integer
n_expected_release tasks offset tau k =
  (Prelude.+) ((\x -> x) (offset tau))
    ((Prelude.*) ((\x -> x) k) ((\x -> x) (task_period (tasks tau))))

n_expected_abs_deadline :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                           Prelude.Integer -> Prelude.Integer
n_expected_abs_deadline tasks offset tau k =
  (Prelude.+) (n_expected_release tasks offset tau k)
    ((\x -> x) (task_relative_deadline (tasks tau)))

n_periodic_dbf_count :: (TaskId -> Task) -> TaskId -> Time -> Prelude.Integer
n_periodic_dbf_count tasks tau h =
  case (Prelude.<) ((\x -> x) h)
         ((\x -> x) (task_relative_deadline (tasks tau))) of {
   Prelude.True -> 0;
   Prelude.False ->
    Prelude.succ
      (div0
        (sub1 ((\x -> x) h) ((\x -> x) (task_relative_deadline (tasks tau))))
        ((\x -> x) (task_period (tasks tau))))}

n_periodic_dbf :: (TaskId -> Task) -> TaskId -> Time -> Prelude.Integer
n_periodic_dbf tasks tau h =
  (Prelude.*) (n_periodic_dbf_count tasks tau h)
    ((\x -> x) (task_cost (tasks tau)))

n_taskset_periodic_dbf :: (TaskId -> Task) -> (List TaskId) -> Time ->
                          Prelude.Integer
n_taskset_periodic_dbf tasks enumT h =
  case enumT of {
   Nil -> 0;
   Cons tau enumT' ->
    (Prelude.+) (n_periodic_dbf tasks tau h)
      (n_taskset_periodic_dbf tasks enumT' h)}

n_periodic_index_in_window :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId
                              -> Time -> Time -> Prelude.Integer ->
                              Prelude.Bool
n_periodic_index_in_window tasks offset tau t1 t2 k =
  (Prelude.&&)
    ((Prelude.<=) ((\x -> x) t1) (n_expected_release tasks offset tau k))
    ((Prelude.<=) (n_expected_abs_deadline tasks offset tau k)
      ((\x -> x) t2))

n_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) -> TaskId ->
                         Time -> Time -> Prelude.Integer
n_periodic_dbf_window tasks offset tau t1 t2 =
  (Prelude.*)
    ((\x -> x)
      (length
        (filter (n_periodic_index_in_window tasks offset tau t1 t2)
          (seq 0 (Prelude.succ t2)))))
    ((\x -> x) (task_cost (tasks tau)))

n_taskset_periodic_dbf_window :: (TaskId -> Task) -> (TaskId -> Time) ->
                                 (List TaskId) -> Time -> Time ->
                                 Prelude.Integer
n_taskset_periodic_dbf_window tasks offset enumT t1 t2 =
  case enumT of {
   Nil -> 0;
   Cons tau enumT' ->
    (Prelude.+) (n_periodic_dbf_window tasks offset tau t1 t2)
      (n_taskset_periodic_dbf_window tasks offset enumT' t1 t2)}

n_dbf_test_upto :: (TaskId -> Task) -> (List TaskId) -> Time -> Prelude.Bool
n_dbf_test_upto tasks enumT h =
  forallb (\t ->
    (Prelude.<=) (n_taskset_periodic_dbf tasks enumT t) ((\x -> x) t))
    (critical_dbf_points_upto tasks (\_ -> 0) enumT h)

n_window_dbf_test_upto :: (TaskId -> Task) -> (TaskId -> Time) -> (List
                          TaskId) -> Time -> Prelude.Bool
n_window_dbf_test_upto tasks offset enumT h =
  forallb (\w ->
    case w of {
     Pair t1 t2 ->
      (Prelude.<=) (n_taskset_periodic_dbf_window tasks offset enumT t1 t2)
        ((\x -> x) (sub t2 t1))})
    (critical_dbf_windows_upto tasks offset enumT h)

n_dbf_test_by_cutoff :: (TaskId -> Task) -> (List TaskId) -> Prelude.Bool
n_dbf_test_by_cutoff tasks enumT =
  n_dbf_test_upto tasks enumT (scalar_dbf_cutoff_bound tasks enumT)

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

extracted_taskset_dbf_test :: (List ExtractedPeriodicTask) -> Prelude.Bool
extracted_taskset_dbf_test ts =
  n_dbf_test_by_cutoff (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts)

edf_schedulability_decide :: (List ExtractedPeriodicTask) -> Prelude.Bool
edf_schedulability_decide ts =
  (Prelude.&&) (extracted_taskset_wf ts) (extracted_taskset_dbf_test ts)

edf_schedulability_counterexample :: (List ExtractedPeriodicTask) -> Option
                                     Time
edf_schedulability_counterexample ts =
  first_dbf_overload_upto (tasks_of_extracted_list ts)
    (enumT_of_extracted_list ts)
    (scalar_dbf_cutoff_bound (tasks_of_extracted_list ts)
      (enumT_of_extracted_list ts))

extracted_offset_window_dbf_test_upto :: (List ExtractedPeriodicTask) -> Time
                                         -> Prelude.Bool
extracted_offset_window_dbf_test_upto ts h =
  n_window_dbf_test_upto (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts) h

extracted_offset_window_dbf_counterexample :: (List ExtractedPeriodicTask) ->
                                              Time -> Option (Prod Time Time)
extracted_offset_window_dbf_counterexample ts h =
  first_window_dbf_overload_upto (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts) h

extracted_offset_window_dbf_decide :: (List ExtractedPeriodicTask) -> Time ->
                                      Prelude.Bool
extracted_offset_window_dbf_decide ts h =
  (Prelude.&&) (extracted_taskset_wf ts)
    (extracted_offset_window_dbf_test_upto ts h)

extracted_offset_window_dbf_cutoff_bound :: (List ExtractedPeriodicTask) ->
                                            Time
extracted_offset_window_dbf_cutoff_bound ts =
  offset_window_dbf_cutoff_bound (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts)

extracted_offset_window_dbf_test_by_cutoff :: (List ExtractedPeriodicTask) ->
                                              Prelude.Bool
extracted_offset_window_dbf_test_by_cutoff ts =
  n_window_dbf_test_upto (tasks_of_extracted_list ts)
    (offset_of_extracted_list ts) (enumT_of_extracted_list ts)
    (extracted_offset_window_dbf_cutoff_bound ts)

extracted_offset_window_dbf_counterexample_by_cutoff :: (List
                                                        ExtractedPeriodicTask)
                                                        -> Option
                                                        (Prod Time Time)
extracted_offset_window_dbf_counterexample_by_cutoff ts =
  extracted_offset_window_dbf_counterexample ts
    (extracted_offset_window_dbf_cutoff_bound ts)

extracted_offset_window_dbf_decide_by_cutoff :: (List ExtractedPeriodicTask)
                                                -> Prelude.Bool
extracted_offset_window_dbf_decide_by_cutoff ts =
  (Prelude.&&) (extracted_taskset_wf ts)
    (extracted_offset_window_dbf_test_by_cutoff ts)

periodic_conservative_schedulability_decide :: (List ExtractedPeriodicTask)
                                               -> Prelude.Bool
periodic_conservative_schedulability_decide =
  edf_schedulability_decide

periodic_conservative_schedulability_counterexample :: (List
                                                       ExtractedPeriodicTask)
                                                       -> Option Time
periodic_conservative_schedulability_counterexample =
  edf_schedulability_counterexample

periodic_offset_window_schedulability_cutoff_bound :: (List
                                                      ExtractedPeriodicTask)
                                                      -> Time
periodic_offset_window_schedulability_cutoff_bound =
  extracted_offset_window_dbf_cutoff_bound

periodic_offset_window_schedulability_decide :: (List ExtractedPeriodicTask)
                                                -> Prelude.Bool
periodic_offset_window_schedulability_decide =
  extracted_offset_window_dbf_decide_by_cutoff

periodic_offset_window_schedulability_counterexample :: (List
                                                        ExtractedPeriodicTask)
                                                        -> Option
                                                        (Prod Time Time)
periodic_offset_window_schedulability_counterexample =
  extracted_offset_window_dbf_counterexample_by_cutoff

extracted_periodic_tasks :: (List ExtractedPeriodicTask) -> TaskId -> Task
extracted_periodic_tasks =
  tasks_of_extracted_list

extracted_periodic_offsets :: (List ExtractedPeriodicTask) -> TaskId -> Time
extracted_periodic_offsets =
  offset_of_extracted_list

extracted_periodic_jobs :: (List ExtractedPeriodicTask) -> JobId -> Job
extracted_periodic_jobs ts =
  canonical_periodic_jobs_from_enumT (extracted_periodic_tasks ts) (\_ -> 0)
    (enumT_of_extracted_list ts)

extracted_offset_periodic_jobs :: (List ExtractedPeriodicTask) -> JobId ->
                                  Job
extracted_offset_periodic_jobs ts =
  canonical_periodic_jobs_from_enumT (extracted_periodic_tasks ts)
    (extracted_periodic_offsets ts) (enumT_of_extracted_list ts)

schedule_of_slots :: (List (Option JobId)) -> Schedule
schedule_of_slots slots t c =
  case (Prelude.==) c 0 of {
   Prelude.True -> nth t slots None;
   Prelude.False -> None}

certified_service_prefix :: (List (Option JobId)) -> JobId -> Time ->
                            Prelude.Integer
certified_service_prefix slots j t =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\t' ->
    (Prelude.+) (certified_service_prefix slots j t')
      (case nth t' slots None of {
        Some j' ->
         case (Prelude.==) j j' of {
          Prelude.True -> Prelude.succ 0;
          Prelude.False -> 0};
        None -> 0}))
    t

certified_completed_by :: (JobId -> Job) -> (List (Option JobId)) -> JobId ->
                          Time -> Prelude.Bool
certified_completed_by jobs slots j t =
  (Prelude.<=) (job_cost (jobs j)) (certified_service_prefix slots j t)

check_prefix_completed_by :: (JobId -> Job) -> (EDFPrefixCert JobId) ->
                             Prelude.Bool
check_prefix_completed_by jobs c =
  forallb (\jt ->
    case jt of {
     Pair j t -> certified_completed_by jobs (prefix_slots c) j t})
    (combine (prefix_basis_jobs c) (prefix_completed_by c))

check_prefix_backlog_row :: (JobId -> Job) -> (List (Option JobId)) -> Time
                            -> (List JobId) -> (List Prelude.Bool) ->
                            Prelude.Bool
check_prefix_backlog_row jobs slots release_time basis row =
  case basis of {
   Nil -> case row of {
           Nil -> Prelude.True;
           Cons _ _ -> Prelude.False};
   Cons jj basis' ->
    case row of {
     Nil -> Prelude.False;
     Cons b row' ->
      (Prelude.&&)
        (case b of {
          Prelude.True -> certified_completed_by jobs slots jj release_time;
          Prelude.False -> Prelude.True})
        (check_prefix_backlog_row jobs slots release_time basis' row')}}

check_prefix_backlog_rows_with_basis :: (JobId -> Job) -> (List
                                        (Option JobId)) -> (List JobId) ->
                                        (List JobId) -> (List
                                        (List Prelude.Bool)) -> Prelude.Bool
check_prefix_backlog_rows_with_basis jobs slots row_basis column_basis rows =
  case row_basis of {
   Nil -> case rows of {
           Nil -> Prelude.True;
           Cons _ _ -> Prelude.False};
   Cons ji basis' ->
    case rows of {
     Nil -> Prelude.False;
     Cons row rows' ->
      (Prelude.&&)
        (check_prefix_backlog_row jobs slots (job_release (jobs ji))
          column_basis row)
        (check_prefix_backlog_rows_with_basis jobs slots basis' column_basis
          rows')}}

check_prefix_backlog_rows :: (JobId -> Job) -> (List (Option JobId)) -> (List
                             JobId) -> (List (List Prelude.Bool)) ->
                             Prelude.Bool
check_prefix_backlog_rows jobs slots basis rows =
  check_prefix_backlog_rows_with_basis jobs slots basis basis rows

check_prefix_backlog_matrix :: (JobId -> Job) -> (EDFPrefixCert JobId) ->
                               Prelude.Bool
check_prefix_backlog_matrix jobs c =
  check_prefix_backlog_rows jobs (prefix_slots c) (prefix_basis_jobs c)
    (prefix_backlog_free_matrix c)

check_prefix_cert_semantic :: (JobId -> Job) -> (EDFPrefixCert JobId) ->
                              Prelude.Bool
check_prefix_cert_semantic jobs c =
  (Prelude.&&)
    ((Prelude.&&) (check_prefix_cert c) (check_prefix_completed_by jobs c))
    (check_prefix_backlog_matrix jobs c)

option_job_eqb :: (Option JobId) -> (Option JobId) -> Prelude.Bool
option_job_eqb x y =
  case x of {
   Some jx ->
    case y of {
     Some jy -> (Prelude.==) jx jy;
     None -> Prelude.False};
   None -> case y of {
            Some _ -> Prelude.False;
            None -> Prelude.True}}

check_prefix_slots_match_generated_edf_fast :: (TaskId -> Task) -> (TaskId ->
                                               Time) -> (JobId -> Job) ->
                                               (List TaskId) -> PeriodicCodec
                                               -> (EDFPrefixCert JobId) ->
                                               Prelude.Bool
check_prefix_slots_match_generated_edf_fast tasks offset jobs enumT codec c =
  (Prelude.&&) (check_prefix_cert c)
    (forallb (\t ->
      option_job_eqb (nth t (prefix_slots c) None)
        (choose_edf jobs (Prelude.succ 0)
          (schedule_of_slots (prefix_slots c)) t
          (periodic_candidates_before tasks offset jobs enumT codec jobs
            (Prelude.succ 0) (schedule_of_slots (prefix_slots c)) t)))
      (seq 0 (prefix_horizon c)))

index_of_job :: JobId -> (List JobId) -> Option Prelude.Integer
index_of_job j basis =
  case basis of {
   Nil -> None;
   Cons j' basis' ->
    case (Prelude.==) j j' of {
     Prelude.True -> Some 0;
     Prelude.False ->
      option_map (\x -> Prelude.succ x) (index_of_job j basis')}}

check_job_in_basis :: (List JobId) -> JobId -> Prelude.Bool
check_job_in_basis basis j =
  case index_of_job j basis of {
   Some _ -> Prelude.True;
   None -> Prelude.False}

check_prefix_backlog_pair :: (EDFPrefixCert JobId) -> JobId -> JobId ->
                             Prelude.Bool
check_prefix_backlog_pair c target earlier =
  case index_of_job target (prefix_basis_jobs c) of {
   Some i ->
    case index_of_job earlier (prefix_basis_jobs c) of {
     Some k ->
      case nth_error (prefix_backlog_free_matrix c) i of {
       Some row ->
        case nth_error row k of {
         Some b -> b;
         None -> Prelude.False};
       None -> Prelude.False};
     None -> Prelude.False};
   None -> Prelude.False}

check_prefix_backlog_free_before_release :: (EDFPrefixCert JobId) -> JobId ->
                                            (List JobId) -> Prelude.Bool
check_prefix_backlog_free_before_release c target relevant_jobs =
  (Prelude.&&) (check_job_in_basis (prefix_basis_jobs c) target)
    (forallb (check_prefix_backlog_pair c target) relevant_jobs)

check_transport_job_witness :: (EDFTransportCert JobId) -> JobId ->
                               Prelude.Bool
check_transport_job_witness c j =
  check_job_in_basis (transport_basis_jobs c) j

check_transport_jobs_witness :: (EDFTransportCert JobId) -> (List JobId) ->
                                Prelude.Bool
check_transport_jobs_witness c jobs =
  forallb (check_transport_job_witness c) jobs

periodic_transport_residue_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                   (JobId -> Job) -> (List TaskId) ->
                                   PeriodicCodec -> Time -> List JobId
periodic_transport_residue_jobs tasks offset jobs enumT codec period =
  flat_map (\_UU03c4_ ->
    map (global_periodic_job_id_of tasks offset jobs codec _UU03c4_)
      (seq 0 period))
    enumT

check_periodic_transport_residue_coverage :: (EDFTransportCert JobId) ->
                                             (List JobId) -> Prelude.Bool
check_periodic_transport_residue_coverage transport_cert residue_jobs =
  (Prelude.&&) (ltb 0 (transport_period transport_cert))
    (check_transport_jobs_witness transport_cert residue_jobs)

check_transport_residue_shifts :: (EDFTransportCert JobId) -> Prelude.Bool
check_transport_residue_shifts transport_cert =
  forallb (\shift -> (Prelude.==) shift (transport_period transport_cert))
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
   Build_EDFWindowTransportTargetCert JobId Prelude.Integer Prelude.Integer 
 (List EDFWindowTransportPairCert)

window_transport_target_job :: EDFWindowTransportTargetCert -> JobId
window_transport_target_job e =
  case e of {
   Build_EDFWindowTransportTargetCert window_transport_target_job0 _ _ _ ->
    window_transport_target_job0}

window_transport_class_id :: EDFWindowTransportTargetCert -> Prelude.Integer
window_transport_class_id e =
  case e of {
   Build_EDFWindowTransportTargetCert _ window_transport_class_id0 _ _ ->
    window_transport_class_id0}

window_transport_shift :: EDFWindowTransportTargetCert -> Prelude.Integer
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
                              EDFWindowTransportPairCert -> Prelude.Bool
check_shifted_job_relation jobs rep target p =
  let {delta = window_transport_delta p} in
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.==) (job_release (jobs target))
          ((Prelude.+) (job_release (jobs rep)) delta))
        ((Prelude.==) (job_abs_deadline (jobs target))
          ((Prelude.+) (job_abs_deadline (jobs rep)) delta)))
      ((Prelude.==) (job_release (jobs (window_target_earlier_job p)))
        ((Prelude.+) (job_release (jobs (window_rep_earlier_job p))) delta)))
    ((Prelude.==) (job_abs_deadline (jobs (window_target_earlier_job p)))
      ((Prelude.+) (job_abs_deadline (jobs (window_rep_earlier_job p)))
        delta))

check_window_transport_target :: (JobId -> Job) -> (EDFTransportCert 
                                 JobId) -> EDFWindowTransportTargetCert ->
                                 Prelude.Bool
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
          (Prelude.&&)
            ((Prelude.&&)
              ((Prelude.==) class_id (window_transport_class_id target_cert))
              ((Prelude.==) shift (window_transport_shift target_cert)))
            (forallb
              (check_shifted_job_relation jobs (transport_rep_job cls)
                (window_transport_target_job target_cert))
              (window_transport_pairs target_cert));
         None -> Prelude.False};
       None -> Prelude.False};
     None -> Prelude.False};
   None -> Prelude.False}

check_window_transport_targets :: (JobId -> Job) -> (EDFTransportCert 
                                  JobId) -> (List
                                  EDFWindowTransportTargetCert) ->
                                  Prelude.Bool
check_window_transport_targets jobs transport_cert target_certs =
  forallb (check_window_transport_target jobs transport_cert) target_certs

check_window_transport_target_entry :: (JobId -> Job) -> (EDFTransportCert
                                       JobId) -> Prelude.Integer ->
                                       Prelude.Integer -> Prelude.Integer ->
                                       EDFWindowTransportTargetCert ->
                                       Prelude.Bool
check_window_transport_target_entry jobs transport_cert target class_id shift target_cert =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.==) (window_transport_target_job target_cert) target)
        ((Prelude.==) (window_transport_class_id target_cert) class_id))
      ((Prelude.==) (window_transport_shift target_cert) shift))
    (check_window_transport_target jobs transport_cert target_cert)

check_window_transport_target_rows_complete :: (JobId -> Job) ->
                                               (EDFTransportCert JobId) ->
                                               (List
                                               EDFWindowTransportTargetCert)
                                               -> (List JobId) -> (List
                                               Prelude.Integer) -> (List
                                               Prelude.Integer) ->
                                               Prelude.Bool
check_window_transport_target_rows_complete jobs transport_cert target_certs basis classes shifts =
  case basis of {
   Nil ->
    case classes of {
     Nil -> case shifts of {
             Nil -> Prelude.True;
             Cons _ _ -> Prelude.False};
     Cons _ _ -> Prelude.False};
   Cons target basis' ->
    case classes of {
     Nil -> Prelude.False;
     Cons class_id classes' ->
      case shifts of {
       Nil -> Prelude.False;
       Cons shift shifts' ->
        case nth_error (transport_classes transport_cert) class_id of {
         Some _ ->
          (Prelude.&&)
            (existsb
              (check_window_transport_target_entry jobs transport_cert target
                class_id shift)
              target_certs)
            (check_window_transport_target_rows_complete jobs transport_cert
              target_certs basis' classes' shifts');
         None -> Prelude.False}}}}

check_window_transport_targets_complete :: (JobId -> Job) ->
                                           (EDFTransportCert JobId) -> (List
                                           EDFWindowTransportTargetCert) ->
                                           Prelude.Bool
check_window_transport_targets_complete jobs transport_cert target_certs =
  (Prelude.&&)
    (check_window_transport_targets jobs transport_cert target_certs)
    (check_window_transport_target_rows_complete jobs transport_cert
      target_certs (transport_basis_jobs transport_cert)
      (transport_job_class transport_cert)
      (transport_job_shift transport_cert))

window_target_candidate_jobs :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (JobId -> Job) -> (List TaskId) ->
                                PeriodicCodec -> JobId -> List JobId
window_target_candidate_jobs tasks offset jobs enumT codec target =
  let {h = Prelude.succ (job_abs_deadline (jobs target))} in
  enum_periodic_jobs_upto tasks offset jobs h enumT
    (periodic_finite_horizon_codec_of tasks offset jobs h codec)

window_target_relevant_earlier_jobs :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (JobId -> Job) -> (List TaskId) ->
                                       PeriodicCodec -> JobId -> List 
                                       JobId
window_target_relevant_earlier_jobs tasks offset jobs enumT codec target =
  filter (\x ->
    (Prelude.&&) (ltb (job_release (jobs x)) (job_release (jobs target)))
      ((Prelude.<=) (job_abs_deadline (jobs x))
        (job_abs_deadline (jobs target))))
    (window_target_candidate_jobs tasks offset jobs enumT codec target)

check_window_target_periodic :: (TaskId -> Task) -> (TaskId -> Time) ->
                                (JobId -> Job) -> (List TaskId) ->
                                PeriodicCodec -> JobId -> Prelude.Bool
check_window_target_periodic tasks offset jobs enumT codec target =
  existsb ((Prelude.==) target)
    (window_target_candidate_jobs tasks offset jobs enumT codec target)

check_window_rep_earlier_membership :: (TaskId -> Task) -> (TaskId -> Time)
                                       -> (JobId -> Job) -> (List TaskId) ->
                                       PeriodicCodec -> JobId ->
                                       EDFWindowTransportPairCert ->
                                       Prelude.Bool
check_window_rep_earlier_membership tasks offset jobs enumT codec rep p =
  existsb ((Prelude.==) (window_rep_earlier_job p))
    (window_target_relevant_earlier_jobs tasks offset jobs enumT codec rep)

check_window_target_rep_earlier_membership :: (TaskId -> Task) -> (TaskId ->
                                              Time) -> (JobId -> Job) ->
                                              (List TaskId) -> PeriodicCodec
                                              -> JobId ->
                                              EDFWindowTransportTargetCert ->
                                              Prelude.Bool
check_window_target_rep_earlier_membership tasks offset jobs enumT codec rep target_cert =
  forallb
    (check_window_rep_earlier_membership tasks offset jobs enumT codec rep)
    (window_transport_pairs target_cert)

check_window_generated_pair_semantics :: (TaskId -> Task) -> (TaskId -> Time)
                                         -> (JobId -> Job) -> (List TaskId)
                                         -> PeriodicCodec ->
                                         (EDFTransportCert JobId) ->
                                         EDFWindowTransportTargetCert ->
                                         Prelude.Bool
check_window_generated_pair_semantics tasks offset jobs enumT codec transport_cert target_cert =
  case nth_error (transport_classes transport_cert)
         (window_transport_class_id target_cert) of {
   Some cls ->
    (Prelude.&&)
      (check_window_target_periodic tasks offset jobs enumT codec
        (window_transport_target_job target_cert))
      (check_window_target_rep_earlier_membership tasks offset jobs enumT
        codec (transport_rep_job cls) target_cert);
   None -> Prelude.False}

check_window_generated_pair_semantics_all :: (TaskId -> Task) -> (TaskId ->
                                             Time) -> (JobId -> Job) -> (List
                                             TaskId) -> PeriodicCodec ->
                                             (EDFTransportCert JobId) ->
                                             (List
                                             EDFWindowTransportTargetCert) ->
                                             Prelude.Bool
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
                                                Prelude.Bool
check_generated_window_pair_target_completed tasks offset jobs enumT codec target p =
  (Prelude.<=) (job_cost (jobs (window_target_earlier_job p)))
    (service_job (Prelude.succ 0)
      (generated_periodic_edf_schedule_upto tasks offset jobs (Prelude.succ
        (job_abs_deadline (jobs target))) enumT codec)
      (window_target_earlier_job p) (job_release (jobs target)))

check_window_generated_pair_completion :: (TaskId -> Task) -> (TaskId ->
                                          Time) -> (JobId -> Job) -> (List
                                          TaskId) -> PeriodicCodec ->
                                          EDFWindowTransportTargetCert ->
                                          Prelude.Bool
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
                                              -> Prelude.Bool
check_window_generated_pair_completion_all tasks offset jobs enumT codec target_certs =
  forallb
    (check_window_generated_pair_completion tasks offset jobs enumT codec)
    target_certs

check_window_transport_pair_for_target_earlier :: (JobId -> Job) -> JobId ->
                                                  JobId -> JobId ->
                                                  EDFWindowTransportPairCert
                                                  -> Prelude.Bool
check_window_transport_pair_for_target_earlier jobs rep target x p =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&) ((Prelude.==) (window_target_earlier_job p) x)
        (ltb (job_release (jobs (window_rep_earlier_job p)))
          (job_release (jobs rep))))
      ((Prelude.<=) (job_abs_deadline (jobs (window_rep_earlier_job p)))
        (job_abs_deadline (jobs rep))))
    (check_shifted_job_relation jobs rep target p)

check_window_target_pair_coverage :: (JobId -> Job) -> JobId ->
                                     EDFWindowTransportTargetCert -> (List
                                     JobId) -> Prelude.Bool
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
                                                     -> Prelude.Bool
check_window_transport_target_complete_with_pairs tasks offset jobs enumT codec transport_cert target_cert =
  case nth_error (transport_classes transport_cert)
         (window_transport_class_id target_cert) of {
   Some cls ->
    (Prelude.&&)
      (check_window_transport_target jobs transport_cert target_cert)
      (check_window_target_pair_coverage jobs (transport_rep_job cls)
        target_cert
        (window_target_relevant_earlier_jobs tasks offset jobs enumT codec
          (window_transport_target_job target_cert)));
   None -> Prelude.False}

check_window_transport_targets_complete_with_pairs :: (TaskId -> Task) ->
                                                      (TaskId -> Time) ->
                                                      (JobId -> Job) -> (List
                                                      TaskId) ->
                                                      PeriodicCodec ->
                                                      (EDFTransportCert
                                                      JobId) -> (List
                                                      EDFWindowTransportTargetCert)
                                                      -> Prelude.Bool
check_window_transport_targets_complete_with_pairs tasks offset jobs enumT codec transport_cert target_certs =
  (Prelude.&&)
    (forallb
      (check_window_transport_target_complete_with_pairs tasks offset jobs
        enumT codec transport_cert)
      target_certs)
    (check_window_transport_target_rows_complete jobs transport_cert
      target_certs (transport_basis_jobs transport_cert)
      (transport_job_class transport_cert)
      (transport_job_shift transport_cert))

check_jobid_not_in :: JobId -> (List JobId) -> Prelude.Bool
check_jobid_not_in j xs =
  forallb (\x -> Prelude.not ((Prelude.==) j x)) xs

check_jobid_list_nodup :: (List JobId) -> Prelude.Bool
check_jobid_list_nodup xs =
  case xs of {
   Nil -> Prelude.True;
   Cons x xs' ->
    (Prelude.&&) (check_jobid_not_in x xs') (check_jobid_list_nodup xs')}

check_transport_basis_nodup :: (EDFTransportCert JobId) -> Prelude.Bool
check_transport_basis_nodup transport_cert =
  check_jobid_list_nodup (transport_basis_jobs transport_cert)

check_transport_class_rep_periodic_generated :: (TaskId -> Task) -> (TaskId
                                                -> Time) -> (JobId -> Job) ->
                                                (List TaskId) ->
                                                PeriodicCodec ->
                                                (EDFTransportClass JobId) ->
                                                Prelude.Bool
check_transport_class_rep_periodic_generated tasks offset jobs enumT codec cls =
  check_window_target_periodic tasks offset jobs enumT codec
    (transport_rep_job cls)

check_transport_classes_rep_periodic_generated :: (TaskId -> Task) -> (TaskId
                                                  -> Time) -> (JobId -> Job)
                                                  -> (List TaskId) ->
                                                  PeriodicCodec -> (List
                                                  (EDFTransportClass JobId))
                                                  -> Prelude.Bool
check_transport_classes_rep_periodic_generated tasks offset jobs enumT codec classes =
  forallb
    (check_transport_class_rep_periodic_generated tasks offset jobs enumT
      codec)
    classes

check_transport_class_rep_backlog :: (EDFPrefixCert JobId) ->
                                     (EDFTransportClass JobId) -> (List
                                     JobId) -> Prelude.Bool
check_transport_class_rep_backlog prefix_cert cls relevant_jobs =
  check_prefix_backlog_free_before_release prefix_cert
    (transport_rep_job cls) relevant_jobs

check_transport_classes_rep_backlog :: (EDFPrefixCert JobId) -> (List
                                       (EDFTransportClass JobId)) -> (List
                                       (List JobId)) -> Prelude.Bool
check_transport_classes_rep_backlog prefix_cert classes class_relevant_jobs =
  case classes of {
   Nil ->
    case class_relevant_jobs of {
     Nil -> Prelude.True;
     Cons _ _ -> Prelude.False};
   Cons cls classes' ->
    case class_relevant_jobs of {
     Nil -> Prelude.False;
     Cons relevant relevant' ->
      (Prelude.&&)
        (check_transport_class_rep_backlog prefix_cert cls relevant)
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
                                               Prelude.Bool
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
                                                 -> Prelude.Bool
check_transport_classes_rep_backlog_generated tasks offset jobs enumT codec prefix_cert classes =
  case classes of {
   Nil -> Prelude.True;
   Cons cls classes' ->
    (Prelude.&&)
      (check_transport_class_rep_backlog_generated tasks offset jobs enumT
        codec prefix_cert cls)
      (check_transport_classes_rep_backlog_generated tasks offset jobs enumT
        codec prefix_cert classes')}

post_reset_target_candidate_horizon :: (TaskId -> Task) -> (List TaskId) ->
                                       Time
post_reset_target_candidate_horizon tasks enumT =
  (Prelude.+)
    ((Prelude.*) (Prelude.succ (Prelude.succ 0))
      (periodic_hyperperiod tasks enumT))
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
                                                 -> Prelude.Bool
check_post_reset_window_target_basis_coverage transport_cert target_certs =
  check_transport_jobs_witness transport_cert
    (post_reset_window_targets_of_certs target_certs)

check_post_reset_target_list_complete :: (List JobId) -> (List
                                         EDFWindowTransportTargetCert) ->
                                         Prelude.Bool
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
                                                       -> Prelude.Bool
check_post_reset_window_targets_complete_with_pairs tasks offset jobs enumT codec transport_cert target_certs =
  (Prelude.&&)
    ((Prelude.&&)
      (check_window_transport_targets_complete_with_pairs tasks offset jobs
        enumT codec transport_cert target_certs)
      (check_window_generated_pair_semantics_all tasks offset jobs enumT
        codec transport_cert target_certs))
    (check_window_generated_pair_completion_all tasks offset jobs enumT codec
      target_certs)

check_hyperperiod_delta_multiple :: (TaskId -> Task) -> (List TaskId) -> Time
                                    -> Prelude.Bool
check_hyperperiod_delta_multiple tasks enumT delta =
  (Prelude.==) delta
    ((Prelude.*) (periodic_hyperperiod tasks enumT)
      (div delta (periodic_hyperperiod tasks enumT)))

check_hyperperiod_shifted_service_pair :: (TaskId -> Task) -> (List TaskId)
                                          -> (JobId -> Job) -> JobId -> JobId
                                          -> JobId -> JobId -> Time ->
                                          Prelude.Bool
check_hyperperiod_shifted_service_pair tasks enumT jobs target x target0 x0 delta =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&) (check_hyperperiod_delta_multiple tasks enumT delta)
            ((Prelude.==) (job_release (jobs target))
              ((Prelude.+) (job_release (jobs target0)) delta)))
          ((Prelude.==) (job_abs_deadline (jobs target))
            ((Prelude.+) (job_abs_deadline (jobs target0)) delta)))
        ((Prelude.==) (job_release (jobs x))
          ((Prelude.+) (job_release (jobs x0)) delta)))
      ((Prelude.==) (job_abs_deadline (jobs x))
        ((Prelude.+) (job_abs_deadline (jobs x0)) delta)))
    ((Prelude.==) (job_cost (jobs x)) (job_cost (jobs x0)))

check_hyperperiod_block_source_pair :: (TaskId -> Task) -> (List TaskId) ->
                                       (JobId -> Job) -> JobId -> JobId ->
                                       JobId -> JobId ->
                                       EDFWindowTransportTargetCert ->
                                       EDFWindowTransportPairCert ->
                                       Prelude.Bool
check_hyperperiod_block_source_pair tasks enumT jobs target x target0 x0 target_cert p =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.==) (window_transport_target_job target_cert) target0)
      ((Prelude.==) (window_target_earlier_job p) x0))
    (check_hyperperiod_shifted_service_pair tasks enumT jobs target x target0
      x0 (window_transport_delta p))

check_hyperperiod_block_source_pair_in_cert :: (TaskId -> Task) -> (List
                                               TaskId) -> (JobId -> Job) ->
                                               JobId -> JobId -> JobId ->
                                               JobId ->
                                               EDFWindowTransportTargetCert
                                               -> Prelude.Bool
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
                                                -> Prelude.Bool
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

type PeriodicFeasibilityCheckedSidecarCert = PeriodicEDFCheckedSidecarCert

extracted_taskset_nonempty :: (List ExtractedPeriodicTask) -> Prelude.Bool
extracted_taskset_nonempty ts =
  ltb 0 (length ts)

extracted_periodic_codec :: (List ExtractedPeriodicTask) -> PeriodicCodec
extracted_periodic_codec ts =
  case ts of {
   Nil -> (\_ _ -> 0);
   Cons e l ->
    zero_offset_periodic_codec_of_tasks (extracted_periodic_tasks (Cons e l))
      (enumT_of_extracted_list (Cons e l))}

extracted_offset_periodic_codec :: (List ExtractedPeriodicTask) ->
                                   PeriodicCodec
extracted_offset_periodic_codec ts =
  case ts of {
   Nil -> (\_ _ -> 0);
   Cons e l ->
    periodic_codec_of_enumT (extracted_periodic_tasks (Cons e l))
      (extracted_periodic_offsets (Cons e l))
      (enumT_of_extracted_list (Cons e l))}

check_periodic_hyperperiod_state_reset :: (TaskId -> Task) -> (TaskId ->
                                          Time) -> (JobId -> Job) -> (List
                                          TaskId) -> PeriodicCodec ->
                                          (EDFPrefixCert JobId) -> Time ->
                                          Prelude.Bool
check_periodic_hyperperiod_state_reset tasks offset jobs enumT codec prefix_cert hyperperiod =
  forallb (\j ->
    certified_completed_by jobs (prefix_slots prefix_cert) j hyperperiod)
    (enum_periodic_jobs_before tasks offset jobs enumT codec hyperperiod)

check_transport_period_is_hyperperiod :: (TaskId -> Task) -> (List TaskId) ->
                                         (EDFTransportCert JobId) ->
                                         Prelude.Bool
check_transport_period_is_hyperperiod tasks enumT transport_cert =
  (Prelude.==) (transport_period transport_cert)
    (periodic_hyperperiod tasks enumT)

check_prefix_horizon_covers_hyperperiod :: (TaskId -> Task) -> (List 
                                           TaskId) -> (EDFPrefixCert 
                                           JobId) -> Prelude.Bool
check_prefix_horizon_covers_hyperperiod tasks enumT prefix_cert =
  (Prelude.<=) (periodic_hyperperiod tasks enumT)
    (prefix_horizon prefix_cert)

post_reset_window_horizon :: (TaskId -> Task) -> (List TaskId) -> Time
post_reset_window_horizon tasks enumT =
  (Prelude.+)
    ((Prelude.*) (Prelude.succ (Prelude.succ 0))
      (periodic_hyperperiod tasks enumT))
    (periodic_max_relative_deadline tasks enumT)

check_prefix_horizon_covers_post_reset_window :: (TaskId -> Task) -> (List
                                                 TaskId) -> (EDFPrefixCert
                                                 JobId) -> Prelude.Bool
check_prefix_horizon_covers_post_reset_window tasks enumT prefix_cert =
  (Prelude.<=) (post_reset_window_horizon tasks enumT)
    (prefix_horizon prefix_cert)

check_periodic_edf_checked_sidecar_with_jobs :: (List ExtractedPeriodicTask)
                                                -> (TaskId -> Time) -> (JobId
                                                -> Job) -> PeriodicCodec ->
                                                (EDFInfiniteCert JobId) ->
                                                PeriodicEDFCheckedSidecarCert
                                                -> Prelude.Bool
check_periodic_edf_checked_sidecar_with_jobs ts offset jobs codec cert sidecar =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        ((Prelude.&&)
          ((Prelude.&&)
            ((Prelude.&&)
              ((Prelude.&&)
                ((Prelude.&&)
                  ((Prelude.&&)
                    ((Prelude.&&)
                      ((Prelude.&&)
                        ((Prelude.&&)
                          ((Prelude.&&)
                            ((Prelude.&&)
                              ((Prelude.&&)
                                ((Prelude.&&)
                                  ((Prelude.&&)
                                    ((Prelude.&&)
                                      ((Prelude.&&)
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
                                      -> Prelude.Bool
check_periodic_edf_checked_sidecar ts codec cert sidecar =
  check_periodic_edf_checked_sidecar_with_jobs ts (\_ -> 0)
    (extracted_periodic_jobs ts) codec cert sidecar

check_periodic_edf_checked_sidecar_extracted :: (List ExtractedPeriodicTask)
                                                -> (EDFInfiniteCert JobId) ->
                                                PeriodicEDFCheckedSidecarCert
                                                -> Prelude.Bool
check_periodic_edf_checked_sidecar_extracted ts cert sidecar =
  (Prelude.&&) (extracted_taskset_nonempty ts)
    (check_periodic_edf_checked_sidecar ts (extracted_periodic_codec ts) cert
      sidecar)

check_periodic_edf_checked_sidecar_extracted_with_offsets :: (List
                                                             ExtractedPeriodicTask)
                                                             ->
                                                             (EDFInfiniteCert
                                                             JobId) ->
                                                             PeriodicEDFCheckedSidecarCert
                                                             -> Prelude.Bool
check_periodic_edf_checked_sidecar_extracted_with_offsets ts cert sidecar =
  (Prelude.&&) (extracted_taskset_nonempty ts)
    (check_periodic_edf_checked_sidecar_with_jobs ts
      (extracted_periodic_offsets ts) (extracted_offset_periodic_jobs ts)
      (extracted_offset_periodic_codec ts) cert sidecar)

check_periodic_feasibility_checked_sidecar_extracted :: (List
                                                        ExtractedPeriodicTask)
                                                        -> (EDFInfiniteCert
                                                        JobId) ->
                                                        PeriodicFeasibilityCheckedSidecarCert
                                                        -> Prelude.Bool
check_periodic_feasibility_checked_sidecar_extracted =
  check_periodic_edf_checked_sidecar_extracted_with_offsets

data PeriodicPolicy =
   PolicyEDF
 | PolicyLLF

check_periodic_policy_feasibility :: PeriodicPolicy -> (List
                                     ExtractedPeriodicTask) ->
                                     (EDFInfiniteCert JobId) ->
                                     PeriodicFeasibilityCheckedSidecarCert ->
                                     Prelude.Bool
check_periodic_policy_feasibility _ =
  check_periodic_feasibility_checked_sidecar_extracted

