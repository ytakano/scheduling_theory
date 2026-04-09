# Scheduling Theory

This project is focused on the formalization of scheduling theory using the Rocq proof assistant.

Core modules are layered as:

```text
Base.v
  -> ScheduleModel.v
  -> SchedulerInterface.v
  -> DispatchInterface.v
  -> DispatchSchedulerBridge.v
  -> EDF.v / FIFO.v / Partitioned.v
```

`SchedulerInterface.v` uses a relation-based scheduler model:

- `scheduler_rel alg jobs m sched`
- `schedulable_by alg jobs m`
- `schedulable_by_on J alg jobs m`

Concrete usage examples live in `SchedulableExamples.v` and `FeasibleExamples.v`.

# Plan

- Roadmap: [plan/roadmap.md](plan/roadmap.md)
- What to Prove: [plan/what_to_prove.md](plan/what_to_prove.md)

# Rocq Compiler

To compile a Rocq file, use the following command:

```text
rocq compile Base.v
rocq compile ScheduleModel.v
rocq compile SchedulerInterface.v
rocq compile DispatchSchedulerBridge.v
rocq compile EDF.v
rocq compile FIFO.v
rocq compile Partitioned.v
```

To compile the main development, run:

```text
make
```

Compilation is the test mechanism in this repository.
