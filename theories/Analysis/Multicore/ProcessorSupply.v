From RocqSched Require Export Multicore.Common.ServiceFacts.

(** * Analysis-facing wrapper for multicore processor-supply facts

    This file intentionally re-exports the policy-independent machine-supply
    theorems from `Multicore.Common.ServiceFacts`.

    The semantic content now lives in the common multicore layer; this module
    remains only as a stable analysis-side import path for downstream clients
    that still expect `Analysis.Multicore.ProcessorSupply`. *)
