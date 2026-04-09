all: EDF.vo example_feasible.vo example_schedulable.vo Partitioned.vo FIFO.vo PeriodicTasks.vo UniSchedulerLemmas.vo

Base.vo: Base.v
	rocq compile Base.v

ScheduleModel.vo: ScheduleModel.v Base.vo
	rocq compile ScheduleModel.v

SchedulerInterface.vo: SchedulerInterface.v ScheduleModel.vo
	rocq compile SchedulerInterface.v

Schedule.vo: Schedule.v ScheduleModel.vo SchedulerInterface.vo
	rocq compile Schedule.v

PeriodicTasks.vo: PeriodicTasks.v Base.vo
	rocq compile PeriodicTasks.v

DispatchInterface.vo: DispatchInterface.v Schedule.vo Base.vo
	rocq compile DispatchInterface.v

UniSchedulerInterface.vo: UniSchedulerInterface.v DispatchInterface.vo
	rocq compile UniSchedulerInterface.v

UniSchedulerLemmas.vo: UniSchedulerInterface.vo
	rocq compile UniSchedulerLemmas.v

EDF.vo: EDF.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile EDF.v

FIFO.vo: FIFO.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile FIFO.v

Partitioned.vo: Partitioned.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile Partitioned.v

example_feasible.vo: example_feasible.v Schedule.vo
	rocq compile example_feasible.v

example_schedulable.vo: example_schedulable.v Schedule.vo
	rocq compile example_schedulable.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
