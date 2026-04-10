# Proof Plan: improve_edf_lemmas

## Goal

Replace `exists_first_edf_violation_before` (which uses `classic`) with a
constructive version `exists_first_edf_violation_before_with` that avoids
classical logic entirely, by grounding violations in finite candidate lists.

## Proof Strategy

1. Define `edf_violation_at_in` / `edf_violation_at_with` (Prop, finite-candidate-based)
2. Prove `matches_choose_edf_at_with_no_finite_violation`
3. Define Boolean versions `edf_violationb_in` / `edf_violationb_at_with`
4. Prove `edf_violationb_in_true_iff` (Boolean ↔ Prop)
5. Define `find_first_in_range` / `first_nat_up_to` with spec lemmas
6. Prove `exists_first_edf_violation_before_with` (constructive, no `classic`)

## Proposed Lemmas

- [x] `edf_violation_at_in` (definition)
- [x] `edf_violation_at_with` (definition)
- [x] `matches_choose_edf_at_with_no_finite_violation`
- [x] `edf_violationb_in` (definition)
- [x] `edf_violationb_at_with` (definition)
- [x] `edf_violationb_in_true_iff`
- [x] `edf_violationb_at_with_true_iff` (corollary)
- [x] `find_first_in_range` (Fixpoint)
- [x] `find_first_in_range_some_spec`
- [x] `find_first_in_range_none_spec`
- [x] `first_nat_up_to` (definition)
- [x] `first_nat_up_to_some_spec`
- [x] `first_nat_up_to_none_spec`
- [x] `exists_first_edf_violation_before_with`

## Proof Order

1. Definitions: `edf_violation_at_in`, `edf_violation_at_with`
2. `matches_choose_edf_at_with_no_finite_violation`
3. Definitions: `edf_violationb_in`, `edf_violationb_at_with`
4. `edf_violationb_in_true_iff`
5. `edf_violationb_at_with_true_iff`
6. `find_first_in_range` (Fixpoint)
7. `find_first_in_range_some_spec`
8. `find_first_in_range_none_spec`
9. `first_nat_up_to`
10. `first_nat_up_to_some_spec`
11. `first_nat_up_to_none_spec`
12. `exists_first_edf_violation_before_with`
