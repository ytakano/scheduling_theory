Require Export DispatchInterface.

(* Backward-compatible aliases for the old names.
   New code should use GenericDispatchSpec / dispatch directly. *)
Abbreviation GenericSchedulerDecisionSpec := GenericDispatchSpec.
Abbreviation mkGenericSchedulerDecisionSpec := mkGenericDispatchSpec.
Abbreviation choose_g := dispatch.
Abbreviation choose_g_ready := dispatch_ready.
Abbreviation choose_g_some_if_ready := dispatch_some_if_ready.
Abbreviation choose_g_none_if_no_ready := dispatch_none_if_no_ready.
Abbreviation choose_g_in_candidates := dispatch_in_candidates.
