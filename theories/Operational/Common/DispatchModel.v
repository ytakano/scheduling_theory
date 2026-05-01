From Stdlib Require Import Bool.

Inductive DispatchModel : Type :=
| StrictDispatchModel
| SpuriousDispatchModel.

Definition dispatch_model_allows_spurious_dispatch
    (model : DispatchModel) : bool :=
  match model with
  | StrictDispatchModel => false
  | SpuriousDispatchModel => true
  end.

Definition dispatch_model_is_strict
    (model : DispatchModel) : bool :=
  negb (dispatch_model_allows_spurious_dispatch model).

