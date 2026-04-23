From Stdlib Require Extraction.
From RocqSched Require Import Operational.Awkernel.Minimal.CapturedTraceSyntax.
From RocqSched Require Import Operational.Awkernel.HandoffTraceFamily.

Extraction Language Haskell.

Extraction "/scheduling_theory/extracted/haskell/AwkernelHandoffAcceptance.hs"
  awk_handoff_accepts_rows.
