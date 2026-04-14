From Stdlib Require Import Arith Arith.PeanoNat Lia.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import Semantics.Schedule.
From RocqSched Require Import Semantics.ScheduleLemmas.ScheduleFacts.
From RocqSched Require Import Multicore.Common.MultiCoreBase.
From RocqSched Require Import Multicore.Common.ServiceFacts.
From RocqSched Require Import Multicore.Common.CompletionFacts.

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

  Example migrating_service_matches_sum_of_cpu_services :
    service_job 2 migrating_sched 0 2 =
    service_sum_on_cpus 2 migrating_sched 0 2.
  Proof.
    apply service_job_eq_sum_of_cpu_services.
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

End GlobalServiceExamples.
