From Stdlib Require Import ExtrHaskellNatInteger.

(* Keep option/list/prod as Rocq-shaped constructors for the handwritten
   Haskell wrappers, but use Prelude booleans so extracted nat comparisons
   compose with boolean checker code. *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive sumbool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant orb => "(Prelude.||)".
Extract Inlined Constant negb => "Prelude.not".
