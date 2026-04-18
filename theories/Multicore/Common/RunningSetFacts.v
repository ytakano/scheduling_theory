From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.

(** Thin public wrappers around running/full vocabulary and machine supply. *)

Lemma running_set_at_intro :
  forall m sched t j,
    running m sched j t ->
    running_set_at m sched t j.
Proof.
  intros m sched t j Hrun.
  exact Hrun.
Qed.

Lemma running_set_at_elim :
  forall m sched t j,
    running_set_at m sched t j ->
    running m sched j t.
Proof.
  intros m sched t j Hrun.
  exact Hrun.
Qed.

Lemma not_machine_full_at_implies_some_cpu_idle :
  forall m sched t,
    ~ machine_full_at m sched t ->
    some_cpu_idle m sched t.
Proof.
  induction m as [|m IH]; intros sched t Hnotfull.
  - exfalso.
    apply Hnotfull.
    intros c Hlt.
    lia.
  - destruct (sched t m) as [j|] eqn:Hlast.
    + assert (Htail_not_full : ~ machine_full_at m sched t).
      { intro Htail.
        apply Hnotfull.
        intros c Hc.
        destruct (Nat.eq_dec c m) as [-> | Hneq].
        - exists j. exact Hlast.
        - apply Htail. lia.
      }
      destruct (IH sched t Htail_not_full) as [c [Hlt Hid]].
      exists c. split; [lia | exact Hid].
    + exists m. split; [lia | exact Hlast].
Qed.

Lemma some_cpu_idle_iff_not_machine_full_at :
  forall m sched t,
    some_cpu_idle m sched t <-> ~ machine_full_at m sched t.
Proof.
  intros m sched t.
  split.
  - intros Hidle Hfull.
    eapply machine_full_at_implies_not_some_cpu_idle; eauto.
  - apply not_machine_full_at_implies_some_cpu_idle.
Qed.

Lemma total_cpu_service_at_eq_m_implies_machine_full_at :
  forall m sched t,
    total_cpu_service_at m sched t = m ->
    machine_full_at m sched t.
Proof.
  induction m as [|m IH]; intros sched t Heq c Hc.
  - lia.
  - simpl in Heq.
    destruct (sched t m) as [j|] eqn:Hlast.
    + destruct (Nat.eq_dec c m) as [-> | Hneq].
      * exists j. exact Hlast.
      * assert (Htail : machine_full_at m sched t).
        { apply IH. lia. }
        apply Htail. lia.
    + pose proof (total_cpu_service_at_le_num_cpus m sched t) as Hle.
      lia.
Qed.

Lemma machine_full_at_iff_total_cpu_service_at_eq_m :
  forall m sched t,
    machine_full_at m sched t <->
    total_cpu_service_at m sched t = m.
Proof.
  intros m sched t.
  split.
  - apply machine_full_at_implies_total_cpu_service_at_eq_m.
  - apply total_cpu_service_at_eq_m_implies_machine_full_at.
Qed.
