# Proof Plan: Improve UniSchedulerLemmas

## Goal

Add new lemmas and definitions to `UniSchedulerLemmas.v` (and prerequisites in other files)
to strengthen the interface for future `Partitioned.v` development.

## Proof Strategy

Implement in dependency order:
1. `Schedule.v`: simple ready/pending decomposition lemmas
2. `UniSchedulerInterface.v`: add `choose_in_candidates` field to record
3. `EDF.v`: prove `choose_edf_in_candidates` + extend `edf_scheduler_spec`
4. `UniSchedulerLemmas.v`: use new field for derived lemmas + coverage definitions

## Proposed Lemmas

### Schedule.v additions
- [ ] `ready_implies_released`: `ready -> released` (proj1 of pending)
- [ ] `ready_implies_not_completed`: `ready -> ~completed` (proj2 of pending)

### UniSchedulerInterface.v addition
- [ ] `choose_in_candidates` field: `choose ... = Some j -> In j candidates`

### EDF.v addition
- [ ] `choose_edf_in_candidates`: min_dl_job_in + filter_In proj1

### UniSchedulerLemmas.v additions
- [ ] `candidates_sound` definition
- [ ] `candidates_complete` definition
- [ ] `choose_some_implies_in_candidates` (E1): uses choose_in_candidates field
- [ ] `exists_ready_candidate_implies_not_none` (E2): ready_exists_implies_choose_some
- [ ] `choose_none_implies_each_candidate_unreleased_or_completed` (E3): classical logic
- [ ] `choose_some_under_sound_candidates` (F3): E1 + A1
- [ ] `choose_some_if_any_ready_under_complete_candidates` (F4): candidates_complete + B1

## Proof Order

1. `ready_implies_released` (Schedule.v)
2. `ready_implies_not_completed` (Schedule.v)
3. `choose_in_candidates` field in UniSchedulerInterface.v
4. `choose_edf_in_candidates` (EDF.v)
5. Extend `edf_scheduler_spec` (EDF.v)
6. `candidates_sound` / `candidates_complete` definitions (UniSchedulerLemmas.v)
7. `choose_some_implies_in_candidates` (UniSchedulerLemmas.v)
8. `exists_ready_candidate_implies_not_none` (UniSchedulerLemmas.v)
9. `choose_none_implies_each_candidate_unreleased_or_completed` (UniSchedulerLemmas.v)
10. `choose_some_under_sound_candidates` (UniSchedulerLemmas.v)
11. `choose_some_if_any_ready_under_complete_candidates` (UniSchedulerLemmas.v)
