From Stdlib Require Import Arith Arith.PeanoNat Lia ZArith.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Analysis.Multicore.Interference.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.CompletionFacts.
From RocqSched Require Import Multicore.Common.RemainingCostFacts.
From RocqSched Require Import Multicore.Common.LaxityFacts.

Section GlobalServiceExamples.

  Definition migrating_job : Job := mkJob 0 0 0 2 3.

  Definition migrating_jobs (_ : JobId) : Job := migrating_job.

  Definition migrating_sched (t : Time) (cpu : CPU) : option JobId :=
    match t, cpu with
    | 0, 0 => Some 0
    | 1, 1 => Some 0
    | _, _ => None
    end.

  Example migrating_schedule_no_duplication :
    no_duplication 2 migrating_sched.
  Proof.
    unfold no_duplication, sequential_jobs, migrating_sched.
    intros j t c1 c2 Hlt1 Hlt2 Hrun1 Hrun2.
    destruct t as [|[|t']].
    - destruct c1 as [|[|c1']]; destruct c2 as [|[|c2']];
        simpl in *; try discriminate; inversion Hrun1; inversion Hrun2; lia.
    - destruct c1 as [|[|c1']]; destruct c2 as [|[|c2']];
        simpl in *; try discriminate; inversion Hrun1; inversion Hrun2; lia.
    - destruct c1 as [|[|c1']]; destruct c2 as [|[|c2']];
        simpl in *; discriminate.
  Qed.

  Example migrating_service_on_cpu0_before_migration :
    service_job 1 (cpu_schedule migrating_sched 0) 0 1 = 1.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example migrating_service_on_cpu1_after_migration :
    service_job 1 (cpu_schedule migrating_sched 1) 0 2 = 1.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example migrating_global_service_is_preserved :
    service_job 2 migrating_sched 0 2 = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example migrating_interval_service_is_preserved :
    service_between 2 migrating_sched 0 0 2 = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example migrating_service_matches_sum_of_cpu_services :
    service_job 2 migrating_sched 0 2 =
    service_sum_on_cpus 2 migrating_sched 0 2.
  Proof.
    apply service_job_eq_sum_of_cpu_services.
  Qed.

  Example migrating_total_cpu_service_between :
    total_cpu_service_between 2 migrating_sched 0 2 = 2.
  Proof.
    reflexivity.
  Qed.

  Example migrating_service_between_bounded_by_machine_supply :
    service_between 2 migrating_sched 0 0 2 <=
    total_cpu_service_between 2 migrating_sched 0 2.
  Proof.
    apply service_between_le_total_cpu_service_between.
    lia.
  Qed.

  Example migrating_machine_supply_bounded_by_capacity :
    total_cpu_service_between 2 migrating_sched 0 2 <= 2 * (2 - 0).
  Proof.
    apply total_cpu_service_between_le_capacity.
  Qed.

  Example migrating_no_duplication_interval_service_bound :
    service_between 2 migrating_sched 0 0 2 <= 2.
  Proof.
    eapply no_duplication_service_between_le_interval_length.
    - apply migrating_schedule_no_duplication.
    - lia.
  Qed.

  Example migrating_completion_via_service_sum :
    completed migrating_jobs 2 migrating_sched 0 2.
  Proof.
    rewrite completed_iff_service_sum_ge_cost.
    unfold migrating_jobs, migrating_job.
    rewrite <- migrating_service_matches_sum_of_cpu_services.
    simpl.
    lia.
  Qed.

  Example migrating_remaining_cost_matches_service_sum :
    remaining_cost migrating_jobs 2 migrating_sched 0 1 =
    job_cost (migrating_jobs 0) - service_sum_on_cpus 2 migrating_sched 0 1.
  Proof.
    apply remaining_cost_eq_job_cost_minus_service_sum.
  Qed.

  Example migrating_remaining_cost_decreases_while_running :
    remaining_cost migrating_jobs 2 migrating_sched 0 1 =
    remaining_cost migrating_jobs 2 migrating_sched 0 0 - 1.
  Proof.
    apply remaining_cost_step_running_mc.
    - apply migrating_schedule_no_duplication.
    - exists 0. split; [lia | reflexivity].
    - rewrite not_completed_iff_service_sum_lt_cost.
      simpl.
      lia.
  Qed.

  Example migrating_laxity_is_preserved_while_running :
    laxity migrating_jobs 2 migrating_sched 0 1 =
    laxity migrating_jobs 2 migrating_sched 0 0.
  Proof.
    apply laxity_step_running_mc.
    - apply migrating_schedule_no_duplication.
    - exists 0. split; [lia | reflexivity].
    - rewrite not_completed_iff_service_sum_lt_cost.
      simpl.
      lia.
  Qed.

  Example migrating_laxity_drops_when_not_running :
    laxity migrating_jobs 2 migrating_sched 0 3 =
    Z.sub (laxity migrating_jobs 2 migrating_sched 0 2) 1.
  Proof.
    apply laxity_step_not_running_mc.
    - apply migrating_schedule_no_duplication.
    - intros [c [Hlt Hrun]].
      destruct c as [|[|c']]; simpl in Hrun; try discriminate; lia.
  Qed.

  Definition duplicate_sched (t : Time) (cpu : CPU) : option JobId :=
    match t, cpu with
    | 0, 0 => Some 0
    | 0, 1 => Some 0
    | _, _ => None
    end.

  Example duplicate_schedule_not_no_duplication :
    ~ no_duplication 2 duplicate_sched.
  Proof.
    unfold not, no_duplication, sequential_jobs, duplicate_sched.
    intro Hdup.
    pose proof (Hdup 0 0 0 1 ltac:(lia) ltac:(lia) eq_refl eq_refl) as Heq.
    lia.
  Qed.

  Example duplicate_schedule_service_sum_step_exceeds_one :
    service_sum_on_cpus 2 duplicate_sched 0 1 = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example duplicate_schedule_breaks_unit_step_bound :
    ~ service_sum_on_cpus 2 duplicate_sched 0 1 <=
      service_sum_on_cpus 2 duplicate_sched 0 0 + 1.
  Proof.
    simpl.
    lia.
  Qed.

  Example duplicate_schedule_interval_service_exceeds_unit_length :
    ~ service_between 2 duplicate_sched 0 0 1 <= 1.
  Proof.
    unfold service_between.
    simpl.
    lia.
  Qed.

  Example duplicate_schedule_machine_supply_on_one_slot :
    total_cpu_service_between 2 duplicate_sched 0 1 = 2.
  Proof.
    reflexivity.
  Qed.

End GlobalServiceExamples.
