From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicWindowDemandBound.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicLLFBridge.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicLLFPrefixCoherence.
From RocqSched Require Export TaskModels.Jitter.JitteredPeriodicLLFInfiniteBridge.

(** * Stable public entry points for jittered-periodic LLF analysis

    This layer exposes the release-jitter LLF schedule family:
    finite-suffix and infinite-prefix generation, finite-to-infinite
    lift, and the scheduler-bridge bridge assumptions needed for the
    window-DBF condition.  Coherence between finite-prefix generation and
    infinite generation is internalized for the jittered candidate source. *)
