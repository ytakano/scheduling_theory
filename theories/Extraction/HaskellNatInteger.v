From Stdlib Require Import ExtrHaskellNatInteger.
From Stdlib Require Import ExtrHaskellZInteger.
From Stdlib Require Import NArith.

(* Keep option/list/prod as Rocq-shaped constructors for the handwritten
   Haskell wrappers, but use Prelude booleans so extracted nat comparisons
   compose with boolean checker code. *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".

(* Stage 2 finite checker kernels may use Rocq's binary natural [N] internally
   while preserving the common nat-facing interface.  Extract those local N
   values to Haskell Integer as well; parser/wrapper code remains responsible
   for rejecting negative external inputs before they enter the extracted
   checker. *)
Extract Inductive N => "Prelude.Integer" [ "0" "(\x -> x)" ]
  "(\fO fP n -> if n Prelude.== 0 then fO () else fP n)".
Extract Inlined Constant N.of_nat => "(\x -> x)".
Extract Inlined Constant N.to_nat => "(\x -> x)".
Extract Inlined Constant N.succ => "Prelude.succ".
Extract Inlined Constant N.add => "(Prelude.+)".
Extract Inlined Constant N.mul => "(Prelude.*)".
Extract Inlined Constant N.min => "Prelude.min".
Extract Inlined Constant N.max => "Prelude.max".
Extract Inlined Constant N.eqb => "(Prelude.==)".
Extract Inlined Constant N.leb => "(Prelude.<=)".
Extract Inlined Constant N.ltb => "(Prelude.<)".
Extract Constant N.compare =>
  "(\n m -> if n Prelude.== m then Eq else if n Prelude.< m then Lt else Gt)".
Extract Constant N.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant N.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant N.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant N.modulo => "(\n m -> if m Prelude.== 0 then n else Prelude.mod n m)".
