# DBF Proof Patterns

This note documents a reusable proof pattern for concrete bounds of the shape

```coq
forall t, periodic_dbf tasks_ex tau t <= t
```

The target audience is library contributors who want a lightweight way to
close concrete classical-DBF obligations without falling back to large
`Nat.div_mod` scripts.

For periodic EDF tutorials, this arithmetic layer is only one half of the proof
pattern. The other half is schedule-local: extract one idle slot from the
generated schedule, then use the public `BusyIntervalLemmas` facts
`idle_slot_not_busy_prefix_candidate` or `idle_slot_not_busy_prefix_witness`
to discharge the busy-prefix side without expanding the whole schedule.

---

## 1. Motivating example

A common tutorial obligation is:

```coq
forall t, periodic_dbf tasks_ex 1 t <= t
```

For a concrete task with:

* `task_cost = 1`
* `task_period = 7`
* `task_relative_deadline = 3`

the definition unfolds to:

```coq
if t <? 3 then 0 else S ((t - 3) / 7)
```

up to trivial `* 1` normalization.

The old proof style expands division facts with `Nat.div_mod` and then asks
`lia` to recover the desired inequality. This works, but it is heavier than
necessary and obscures the real structure of the argument.

---

## 2. Recommended proof decomposition

The lightweight proof pattern is:

1. unfold `periodic_dbf`,
2. case-split on `t <? task_relative_deadline`,
3. solve the below-deadline branch immediately,
4. normalize away `* 1`,
5. reduce the remaining goal to an upper bound on the division term,
6. use a shared arithmetic lemma instead of re-deriving division algebra.

For the motivating example, the interesting branch becomes:

```coq
S ((t - 3) / 7) <= t
```

Rewrite this as:

```coq
1 + ((t - 3) / 7) <= t
```

and then use:

```coq
div_le_self : forall n d, 0 < d -> n / d <= n
```

to obtain:

```coq
1 + ((t - 3) / 7) <= 1 + (t - 3) <= t
```

This is the entire argument.

---

## 3. Shared helper lemmas

The intended shared helpers live in:

* [DemandBound.v](/scheduling_theory/theories/Analysis/Uniprocessor/DemandBound.v)

The current lightweight pattern uses:

```coq
div_le_self : forall n d, 0 < d -> n / d <= n
div_mul_le_self : forall n d, 0 < d -> d * (n / d) <= n
```

Use `div_le_self` for single-task goals such as:

```coq
forall t, periodic_dbf tasks_ex tau t <= t
```

Use `div_mul_le_self` when a task-set proof needs a stronger aggregate bound
than `q <= n`, for example when combining two DBF terms in one `lia` finish.

---

## 4. Compact proof skeleton

The recommended proof shape is:

```coq
Lemma periodic_dbf_task1_ex_le :
  forall t,
    periodic_dbf tasks_ex 1 t <= t.
Proof.
  intros t.
  unfold periodic_dbf, tasks_ex, task1_ex.
  cbn [tasks_ex task1_ex task_relative_deadline task_period task_cost].
  destruct (t <? 3) eqn:Hlt.
  - apply Nat.le_0_l.
  - apply Nat.ltb_ge in Hlt.
    change (S (((t - 3) / 7) * 1) <= t).
    replace (((t - 3) / 7) * 1) with ((t - 3) / 7) by lia.
    replace (S ((t - 3) / 7)) with (1 + ((t - 3) / 7)) by lia.
    eapply Nat.le_trans.
    + apply Nat.add_le_mono_l.
      apply div_le_self.
      lia.
    + lia.
Qed.
```

This keeps the proof aligned with the semantic meaning of the DBF:

* first eliminate the impossible branch,
* then bound the count of jobs by a simple arithmetic upper bound.

---

## 5. Aggregate task-set DBF bounds

For concrete task sets, the aggregate goal

```coq
forall t, taskset_periodic_dbf tasks_ex enumT_ex t <= t
```

should usually be proved by:

1. proving one lemma per task,
2. reusing those lemmas in the mixed branches,
3. using `div_mul_le_self` only when the combined arithmetic needs a stronger
   estimate than `n / d <= n`.

Do not inline a fresh `Nat.div_mod` argument in every branch of the aggregate
proof. If a branch needs more than `div_le_self`, extract the stronger fact as
its own shared arithmetic helper.

---

## 6. Why `stdpp` is not the right tool here

`stdpp` is useful in this repository for finite maps, sets, domains, and
associated automation. This DBF proof shape is different:

* the difficulty is pure `nat` arithmetic,
* the critical step is bounding `/` on naturals,
* no map/set/domain normalization is involved.

Accordingly, `stdpp` does not make this proof materially shorter or clearer.
The right abstraction is a small arithmetic lemma in the DBF layer.

---

## 7. Worked examples

See the infinite tutorial developments for concrete uses of this pattern:

* [EDFInfiniteSchedulability.v](/scheduling_theory/Tutorials/EDFInfiniteSchedulability.v)
* [LLFInfiniteSchedulability.v](/scheduling_theory/Tutorials/LLFInfiniteSchedulability.v)

These files show both:

* a per-task DBF upper bound using `div_le_self`,
* an aggregate classical-DBF bound that reuses the per-task structure instead
  of rebuilding heavy division proofs from scratch.
