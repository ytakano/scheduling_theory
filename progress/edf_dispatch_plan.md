# Proof Plan: EDF Dispatch Correctness

## Goal

Prove that `choose_edf` (defined in `EDF.v`) satisfies three dispatch correctness properties:

1. **Readiness soundness**: `choose_edf ... = Some j -> ready jobs m sched j t`
2. **Deadline minimality**: `choose_edf ... = Some j -> In j' candidates -> ready ... j' -> dl(j) <= dl(j')`
3. **Selection completeness**: `(exists j, In j candidates /\ ready ... j) -> exists j', choose_edf ... = Some j'`

## Definitions (in `EDF.v`)

### `readyb`
```coq
Definition readyb (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                   (j : JobId) (t : Time) : bool :=
  (job_release (jobs j) <=? t) &&
  negb (job_cost (jobs j) <=? service_job m sched j t).
```

### `min_dl_job`
```coq
Fixpoint min_dl_job (jobs : JobId -> Job) (l : list JobId) : option JobId :=
  match l with
  | []       => None
  | j :: rest =>
    match min_dl_job jobs rest with
    | None    => Some j
    | Some j' => if job_abs_deadline (jobs j) <=? job_abs_deadline (jobs j')
                 then Some j
                 else Some j'
    end
  end.
```

### `choose_edf`
```coq
Definition choose_edf (jobs : JobId -> Job) (m : nat) (sched : Schedule)
                       (t : Time) (candidates : list JobId) : option JobId :=
  min_dl_job jobs (filter (fun j => readyb jobs m sched j t) candidates).
```

## Proof Strategy

Two-phase decomposition:
1. Prove structural properties of `min_dl_job` by induction on the list.
2. Derive top-level dispatch theorems by composing `min_dl_job` properties with `filter_In` and `readyb_iff`.

## Proposed Lemmas

- [x] `readyb_iff`: `readyb jobs m sched j t = true <-> ready jobs m sched j t`
- [x] `min_dl_job_none_iff`: `min_dl_job jobs l = None <-> l = []`
- [x] `min_dl_job_in`: `min_dl_job jobs l = Some j -> In j l`
- [x] `min_dl_job_min`: `min_dl_job jobs l = Some j -> forall j', In j' l -> job_abs_deadline (jobs j) <= job_abs_deadline (jobs j')`
- [x] `choose_edf_ready`: `choose_edf ... = Some j -> ready jobs m sched j t`
- [x] `choose_edf_min_deadline`: `choose_edf ... = Some j -> In j' candidates -> ready ... j' -> dl(j) <= dl(j')`
- [x] `choose_edf_some_if_exists`: `(exists j, In j candidates /\ ready ... j) -> exists j', choose_edf ... = Some j'`

## Proof Order

1. `readyb_iff`
2. `min_dl_job_none_iff`
3. `min_dl_job_in`
4. `min_dl_job_min`
5. `choose_edf_ready`
6. `choose_edf_min_deadline`
7. `choose_edf_some_if_exists`

## Key stdlib lemmas

- `filter_In : In x (filter f l) <-> In x l /\ f x = true`
- `Bool.andb_true_iff`, `Bool.negb_true_iff`, `Bool.not_true_iff_false`
- `Nat.leb_le : (n <=? m) = true <-> n <= m`

## Compilation check

```bash
rocq compile Base.v && rocq compile Schedule.v && rocq compile scheduling.v && rocq compile EDF.v
```
