# Analysis

## Scope

This document describes the analysis layer of the current repository.

Its scope is:

- `theories/Analysis/Common/*`
- `theories/Analysis/Uniprocessor/*`
- `theories/Analysis/Multicore/*`

This layer hosts reusable interval-based schedulability reasoning built on top of semantic schedules and scheduler theorem layers.

## Purpose of the Analysis layer

The analysis layer packages concepts and lemmas used to reason about schedulability over intervals without mixing them into schedule semantics or scheduler implementation correctness.

Its job is to host reusable analysis notions such as:

- busy intervals, busy windows, and busy prefixes,
- processor demand, request bound, and demand bound,
- processor supply and interference,
- workload absorption and fairness-facing contradiction hooks.

The layer is organized so that policy theorem layers remain structural and analysis clients can import packaged entry points instead of rebuilding interval arguments from scratch.

For periodic EDF, the current direction is to keep the finite-horizon
window-DBF bridge as the analysis core and layer infinite-time no-miss /
feasible / schedulable wrappers on top via prefix reuse, rather than replacing
the existing finite theorem family.

For concrete periodic task sets, the preferred downstream path is now to
discharge finite-horizon DBF obligations through the bounded checker layer in
`TaskModels/Periodic/PeriodicConcreteAnalysis.v`, and then feed the resulting
bounded theorem into the existing finite EDF/LLF bridge theorems.

For infinite-time zero-offset classical DBF clients, the same helper layer now
provides a conservative finite cutoff theorem so downstream proofs can replace
`forall t` obligations with a finite `vm_compute` check.

### Example: Busy Intervals, a Busy Window, and Busy Prefixes

```
(I: Idle, B: Busy)

CPU | I | I | I | B | B | B | B | I | I | I
Time|   |   |t0 |t1 |t2 |t3 |t4 |t5 |   |

Busy intervals: [t1, t4), [t1, t3), [t2, t4), etc.
Busy window: [t1, t5)
  (1) CPU must be idle at t0 or t1 == 0
  (2) CPU must be idle at t5
  (3) [t1, t5) is busy interval
Busy prefixes: [t1, t2), [t1, t3), [t1, t4), [t1, t5)
  (1) CPU must be idle at t0 or t1 == 0
  (2) [t1, t2), [t1, t3), [t1, t4), and [t1, t5) are busy intervals
```

- $\text{BusyIntervals} = \{[t_a,t_b)\mid t_1 \le t_a < t_b \le t_5\}$
- $\text{BusyWindow} = [t_1,t_5)$
- $\text{BusyPrefixes} = \{[t_1,t)\mid t_1 < t \le t_5\}$

### Example: Request Bound, Demand Bound, and Processor Demand

Consider the following periodic task set:

```math
\tau_1 = (C_1 = 2,\; T_1 = 5,\; D_1 = 5),\\
\tau_2 = (C_2 = 1,\; T_2 = 4,\; D_2 = 3).
```

where $C_i$, $T_i$, and $D_i$ denote the execution cost, period, and relative deadline of task $\tau_i$, respectively.

Let the analysis-window length be

$H = 5$

For this window:

- task $\tau_1$ can release at most one job in any window of length $5$,
  and that job also has its deadline within the window;
- task $\tau_2$ can release at most two jobs in a window of length $5$,
  but only one of them must have its deadline within the window.

#### Request Bound

Request bound is an upper bound on the amount of execution that may be requested within the interval.

```math
\mathrm{RBF}_{\tau_1}(H)
=
\left\lceil \frac{H}{5} \right\rceil \cdot 2
=
\left\lceil \frac{5}{5} \right\rceil \cdot 2
=
2,
```

So, task $\tau_1$ may request up to $2$ units of execution in any window of length $5$.

```math
\mathrm{RBF}_{\tau_2}(H)
=
\left\lceil \frac{H}{4} \right\rceil \cdot 1
=
\left\lceil \frac{5}{4} \right\rceil \cdot 1
=
2.
```

So, task $\tau_2$ may request up to $2$ units of execution in any window of length $5$.

As a result, the total request bound is

```math
\mathrm{RBF}_{\tau_1}(5) + \mathrm{RBF}_{\tau_2}(5) = 4.
```

#### Demand Bound

Demand bound is the amount of execution that must be completed within the window for jobs whose deadlines fall within that window.

```math
\mathrm{DBF}_{\tau_1}(H)
=
\left(\left\lfloor \frac{H - 5}{5} \right\rfloor + 1\right)\cdot 2
=
\left(\left\lfloor \frac{5 - 5}{5} \right\rfloor + 1\right)\cdot 2
=
2,
```

```math
\mathrm{DBF}_{\tau_2}(H)
=
\left(\left\lfloor \frac{H - 3}{4} \right\rfloor + 1\right)\cdot 1
=
\left(\left\lfloor \frac{5 - 3}{4} \right\rfloor + 1\right)\cdot 1
=
1.
```

So the total demand bound is

```math
\mathrm{DBF}_{\tau_1}(5) + \mathrm{DBF}_{\tau_2}(5) = 3.
```

Besides the usual DBF indexed by a window length $H$, we also use a
**window-DBF**, which fixes a concrete interval $[t_1,t_2)$.
It measures the amount of execution that must be completed within that
specific window for jobs whose deadlines fall in $[t_1,t_2)$.
Hence, scalar DBF is length-based, whereas window-DBF is interval-based.
Under regular release patterns such as zero-offset periodic task sets,
the interval-based view often collapses to the usual scalar DBF.

#### Processor Demand

For periodic task sets, processor demand is instantiated as the sum of the tasks' demand bounds.
For the task set $\Gamma = \{\tau_1,\tau_2\}$, the processor demand over a window of length $5$ is

```math
\mathrm{PD}_{\Gamma}(5)
=
\sum_{\tau \in \Gamma} \mathrm{DBF}_{\tau}(5)
=
3.
```

Therefore,

- **request bound** over-approximates how much work may be released: $4$
- **demand bound** over-approximates how much work must finish within the window: $3$
- **processor demand** is the task-set sum of demand bounds: $3$

In this example,

```math
\mathrm{PD}_{\Gamma}(5)
=
3
\;\le\;
4
=
\mathrm{RBF}_{\tau_1}(5) + \mathrm{RBF}_{\tau_2}(5).
```

### Example: Processor Supply and Interference

Here, **processor supply** means the total amount of service provided by the processors over an interval, whereas **interference** means the part of that supply consumed by jobs other than a given target job.

Consider a two-processor platform and the interval $[t_1,t_4)$.

```text
CPU 1| x | x | x |
CPU 2| y | z | y |
Time |t1 |t2 |t3 | t4
```

In this example, the machine provides one unit of execution per processor and per time slot.
Hence, over the interval $[t_1,t_4)$, the total **processor supply** is

```math
2 \cdot (t_4 - t_1) = 6.
```

A job is **pending** if it has been released but has not yet completed, and it is **eligible** if it is pending and permitted to execute under the scheduler state.

Now consider a target job $j$ that is pending throughout $[t_1,t_4)$ but does not execute in the interval.
Then all supplied service is consumed by other jobs, namely $x$, $y$, and $z$.

This motivates the notion of **interference**: the execution of other jobs occupies processor supply that could otherwise have been available to the target job.
In this example, the jobs $x$, $y$, and $z$ collectively account for all supply in $[t_1,t_4)$, and thus fully interfere with job $j$ over the interval.

### Example: Workload Absorption and a Fairness-Facing Contradiction

A **covering workload** is a set of jobs whose execution accounts for the occupied processor slots in the interval of interest, and a **fairness-facing contradiction hook** is the proof pattern that assumes an eligible job never executes, absorbs the interval's supply into such a covering workload, and then derives a contradiction from an independent upper bound on that workload.

Continuing the previous example, suppose that job $j$ is eligible throughout $[t_1,t_4)$ but never executes.

Since every processor slot in the interval is occupied by jobs $x$, $y$, and $z$, the full processor supply is **absorbed** by their workload.
That is, all $6$ units of service provided by the machine are accounted for by the covering workload $L = \{x, y, z\}$.

Now suppose that, independently of the assumption that job $j$ never executes,
a previously established workload bound shows that the jobs in $L$ can account for at most $5$ units of execution in $[t_1,t_4)$.
Since workload absorption implies that $L$ must account for all $6$ units of processor supply in the interval, we obtain a contradiction:

```math
\text{processor supply in } [t_1,t_4) = 6
\qquad\text{but}\qquad
\text{workload of } L \le 5.
```

Therefore, the assumption that job $j$ remains eligible and yet never executes throughout the interval cannot be correct.

This is the basic proof pattern behind **workload absorption** and **fairness-facing contradiction hooks**:
first account for processor supply via covering interference, and then close the argument by contradicting an external workload bound.

## Core concepts and guarantees

The current analysis layer is split into three sublayers.

`Analysis/Common`
- shared workload aggregation and arithmetic-facing helpers used by multiple clients

`Analysis/Uniprocessor`
- busy-interval and busy-window reasoning
- response-time and search-space reduction lemmas
- processor-demand, request-bound, and demand-bound facts
- EDF-facing processor-demand wrappers and packaged busy-prefix bridges

`Analysis/Multicore`
- processor-supply accounting
- interference and covering-list reasoning
- workload absorption
- fairness contradiction and must-run client theorems
- packaged multicore global analysis entry points

Two packaged public boundaries are especially important:

- `TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v` for the current periodic EDF processor-demand / busy-prefix line
- `Analysis/Multicore/GlobalAnalysisEntryPoints.v` for the current multicore global-analysis line

For concrete periodic analysis, `TaskModels/Periodic/PeriodicConcreteAnalysis.v`
now complements the periodic EDF/LLF entry points with finite-horizon boolean
DBF and window-DBF checks.

The design rule is bridge-first packaging:

- expose packaged bridge records and entry-point modules as the default API,
- keep compatibility wrappers and internal helper lemmas out of the primary downstream surface.

## Public entry points

The main public entry points for this layer are:

- `theories/Analysis/Uniprocessor/BusyWindowSearch.v`
- `theories/Analysis/Uniprocessor/EDFProcessorDemand.v`
- `theories/Analysis/Multicore/GlobalAnalysisEntryPoints.v`
- `theories/TaskModels/Periodic/PeriodicEDFAnalysisEntryPoints.v`

Additional foundational modules include:

- `theories/Analysis/Common/WorkloadAggregation.v`
- `theories/Analysis/Uniprocessor/BusyInterval.v`
- `theories/Analysis/Uniprocessor/ProcessorDemand.v`
- `theories/Analysis/Uniprocessor/RequestBound.v`
- `theories/Analysis/Uniprocessor/DemandBound.v`
- `theories/Analysis/Multicore/ProcessorSupply.v`
- `theories/Analysis/Multicore/Interference.v`
- `theories/Analysis/Multicore/GlobalWorkloadAbsorption.v`
- `theories/Analysis/Multicore/GlobalFairness.v`

## Design boundaries

This layer includes:

- analysis concepts and interval lemmas,
- packaged analysis-facing bridges,
- workload and supply/demand accounting,
- fairness-facing client theorems built from those analysis concepts.

This layer does not include:

- the definition of schedule meaning,
- scheduler implementation correctness or executable-to-spec refinement,
- policy-local chooser proofs,
- task-generation semantics themselves.

Those belong respectively to:

- `design/Semantics.md`
- `design/Refinement.md`
- `design/Uniprocessor.md` and `design/Multicore.md`
- `design/TaskModels.md`

In particular, analysis is not the same as refinement. Analysis proves interval reasoning and deadline-related consequences assuming semantic schedules and theorem-layer boundaries; refinement proves that implementation-facing behavior matches those abstract boundaries.

## Extension points

The current analysis layer is ready to expand in several ways:

- more packaged entry points for sporadic and jitter-aware analysis clients,
- richer multicore tardiness and interference bounds,
- delay-aware analysis that consumes explicit operational or refinement-side delay parameters,
- stronger reuse between uniprocessor and multicore interval reasoning.

These extensions should keep the same discipline: put analysis facts in `Analysis`, not in the policy theorem files that happen to consume them.

## File map

- `theories/Analysis/Common/WorkloadAggregation.v`
  Shared workload aggregation and arithmetic helpers.
- `theories/Analysis/Uniprocessor/BusyInterval.v`
  Busy-interval definitions and first-layer facts.
- `theories/Analysis/Uniprocessor/BusyIntervalLemmas.v`
  Supporting busy-interval lemmas.
- `theories/Analysis/Uniprocessor/BusyWindowSearch.v`
  Busy-window and busy-prefix search interfaces.
- `theories/Analysis/Uniprocessor/ProcessorDemand.v`
  Generic processor-demand reasoning.
- `theories/Analysis/Uniprocessor/RequestBound.v`
  Request-bound functions and associated lemmas.
- `theories/Analysis/Uniprocessor/DemandBound.v`
  Demand-bound interfaces and lemmas.
- `theories/Analysis/Uniprocessor/ResponseTimeSearch.v`
  Response-time search-space infrastructure.
- `theories/Analysis/Uniprocessor/EDFProcessorDemand.v`
  EDF-facing processor-demand wrappers and packaged busy-prefix bridges.
- `theories/Analysis/Multicore/ProcessorSupply.v`
  Machine-supply accounting over intervals.
- `theories/Analysis/Multicore/Interference.v`
  Interference and covering-list infrastructure.
- `theories/Analysis/Multicore/GlobalWorkloadAbsorption.v`
  Workload-absorption bridge layer above supply and interference facts.
- `theories/Analysis/Multicore/GlobalFairness.v`
  Fairness-facing contradiction and must-run clients.
- `theories/Analysis/Multicore/GlobalAnalysisEntryPoints.v`
  Canonical downstream import for the current multicore global-analysis theorem layer.

## Summary

The analysis layer is where interval-based schedulability reasoning lives.

It sits above schedule semantics and scheduler theorem layers, exposes packaged public entry points, and keeps analysis concepts separate from both scheduler implementation correctness and task-generation semantics.
