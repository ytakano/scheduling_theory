# Proof Plan: FIFO Scheduler (FIFO.v)

## Goal

Implement `choose_fifo` (linear-scan FIFO dispatch) and prove it satisfies
`GenericSchedulerDecisionSpec` (4-spec interface in `UniSchedulerInterface.v`).
Also prove the FIFO-specific invariant `choose_fifo_first_ready`.

## Proof Strategy

- Move `readyb` / `readyb_iff` from `EDF.v` → `Schedule.v` (they are policy-independent)
- Create `FIFO.v` modeled on `EDF.v`
- `choose_fifo`: fixpoint linear scan — return first `readyb`-true job in candidate list
- Prove 4 GenericSchedulerDecisionSpec specs by induction on candidates list, branching on `readyb`
- Prove `choose_fifo_first_ready` (FIFO-specific: chosen job is the first ready in order)
- Add concrete example

## Proposed Lemmas

- [x] Step 0: Move `readyb` / `readyb_iff` to `Schedule.v`, update `EDF.v`
- [x] `choose_fifo_ready`: chosen job is ready
- [x] `choose_fifo_none_if_no_ready`: no ready ⟹ None
- [x] `choose_fifo_some_if_exists`: exists ready ⟹ Some
- [x] `choose_fifo_in_candidates`: chosen job ∈ candidates
- [x] `fifo_generic_spec`: assembles GenericSchedulerDecisionSpec
- [x] `choose_fifo_first_ready`: FIFO-specific ordering invariant
- [x] `choose_fifo_example`: concrete example

## Proof Order

1. Move `readyb` / `readyb_iff` (refactor, no new proof)
2. `choose_fifo_ready`
3. `choose_fifo_none_if_no_ready`
4. `choose_fifo_some_if_exists` (by contrapositive of #3)
5. `choose_fifo_in_candidates`
6. `fifo_generic_spec` (assembly)
7. `choose_fifo_first_ready`
8. `choose_fifo_example`
