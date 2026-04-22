From Stdlib Require Import List.
From RocqSched Require Import Foundation.Base.
From RocqSched Require Import TaskModels.Periodic.PeriodicEDFCertificate.

Import ListNotations.

Definition cert_ex_prefix_slots_data : list (option JobId) :=
  [ Some 0; Some 1; None; None; None;
    Some 2; None; Some 3; None; None;
    Some 4; None; None; None; Some 5;
    Some 6; None; None; None; None;
    Some 8; Some 7; None; None; None;
    Some 10; None; None; Some 9; None;
    Some 12; None; None; None; None;
    Some 14; Some 11; None ].

Definition cert_ex_prefix_basis_jobs_data : list JobId :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14].

Definition cert_ex_prefix_completed_by_data : list Time :=
  [3; 4; 8; 11; 13; 18; 18; 25; 23; 32; 28; 39; 33; 38].

Definition cert_ex_prefix_backlog_matrix_data : list (list bool) :=
  [ [false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [false; false; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; false; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; false; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; false; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; false; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; false; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; false; true; false; false; false; false; false];
    [true; true; true; true; true; true; true; false; false; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; false; true; false; false; false];
    [true; true; true; true; true; true; true; true; true; false; false; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; false; true; false];
    [true; true; true; true; true; true; true; true; true; true; true; false; false; false];
    [true; true; true; true; true; true; true; true; true; true; true; false; true; false] ].

Definition cert_ex_task0_shift_data : nat := 7.
Definition cert_ex_task1_shift_data : nat := 5.

Definition cert_ex_task0_completion_offsets_data : list nat :=
  [1; 1; 1; 1; 1; 1; 1].

Definition cert_ex_task1_completion_offsets_data : list nat :=
  [2; 1; 1; 1; 1].

Definition cert_ex_task0_backlog_offsets_data : list nat :=
  [1; 1; 1; 1; 1; 1; 1].

Definition cert_ex_task1_backlog_offsets_data : list nat :=
  [2; 1; 1; 1; 1].

Definition cert_ex_transport_period_data : Time := 35.

Definition cert_ex_transport_classes_data : list (EDFTransportClass JobId) :=
  [ {| transport_rep_job := 0; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 1; transport_completion_offset := 2; transport_backlog_offset := 2 |};
    {| transport_rep_job := 2; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 3; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 4; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 5; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 6; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 7; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 8; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 9; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 10; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 11; transport_completion_offset := 2; transport_backlog_offset := 2 |};
    {| transport_rep_job := 12; transport_completion_offset := 1; transport_backlog_offset := 1 |};
    {| transport_rep_job := 14; transport_completion_offset := 1; transport_backlog_offset := 1 |} ].

Definition cert_ex_transport_job_class_data : list nat :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13].

Definition cert_ex_transport_job_shift_data : list nat :=
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].

Definition cert_ex_dbf_cutoff_data : Time := 0.
Definition cert_ex_dbf_ok_table_data : list bool := [true].

Definition cert_ex_prefix_generic : EDFPrefixCert JobId :=
  {| prefix_horizon := 38;
     prefix_basis_jobs := cert_ex_prefix_basis_jobs_data;
     prefix_slots := cert_ex_prefix_slots_data;
     prefix_completed_by := cert_ex_prefix_completed_by_data;
     prefix_backlog_free_matrix := cert_ex_prefix_backlog_matrix_data |}.

Definition cert_ex_transport_generic : EDFTransportCert JobId :=
  {| transport_period := cert_ex_transport_period_data;
     transport_basis_jobs := cert_ex_prefix_basis_jobs_data;
     transport_classes := cert_ex_transport_classes_data;
     transport_job_class := cert_ex_transport_job_class_data;
     transport_job_shift := cert_ex_transport_job_shift_data |}.

Definition cert_ex_dbf_generic : EDFDBFCert :=
  {| dbf_cutoff := cert_ex_dbf_cutoff_data;
     dbf_ok_table := cert_ex_dbf_ok_table_data |}.

Definition cert_ex_generic : EDFInfiniteCert JobId :=
  {| cert_prefix := cert_ex_prefix_generic;
     cert_transport := cert_ex_transport_generic;
     cert_dbf := cert_ex_dbf_generic |}.
