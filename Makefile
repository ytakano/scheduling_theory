all: EDF.vo FeasibleExamples.vo SchedulableExamples.vo Partitioned.vo FIFO.vo FIFOExamples.vo PeriodicTasks.vo UniSchedulerLemmas.vo UniSchedulerLemmasClassical.vo

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

UniSchedulerLemmasClassical.vo: UniSchedulerLemmasClassical.v UniSchedulerLemmas.vo
	rocq compile UniSchedulerLemmasClassical.v

EDF.vo: EDF.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile EDF.v

FIFO.vo: FIFO.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile FIFO.v

FIFOExamples.vo: FIFOExamples.v FIFO.vo Schedule.vo Base.vo
	rocq compile FIFOExamples.v

Partitioned.vo: Partitioned.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile Partitioned.v

FeasibleExamples.vo: FeasibleExamples.v Schedule.vo
	rocq compile FeasibleExamples.v

SchedulableExamples.vo: SchedulableExamples.v Schedule.vo
	rocq compile SchedulableExamples.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
