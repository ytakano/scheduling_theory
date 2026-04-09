all: EDF.vo FeasibleExamples.vo SchedulableExamples.vo Partitioned.vo FIFO.vo FIFOExamples.vo PeriodicTasks.vo DispatchLemmas.vo DispatchClassicalLemmas.vo

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

DispatchLemmas.vo: DispatchLemmas.v DispatchInterface.vo
	rocq compile DispatchLemmas.v

DispatchClassicalLemmas.vo: DispatchClassicalLemmas.v DispatchLemmas.vo
	rocq compile DispatchClassicalLemmas.v

EDF.vo: EDF.v Schedule.vo Base.vo DispatchInterface.vo
	rocq compile EDF.v

FIFO.vo: FIFO.v Schedule.vo Base.vo DispatchInterface.vo
	rocq compile FIFO.v

FIFOExamples.vo: FIFOExamples.v FIFO.vo Schedule.vo Base.vo
	rocq compile FIFOExamples.v

Partitioned.vo: Partitioned.v Schedule.vo Base.vo DispatchInterface.vo
	rocq compile Partitioned.v

FeasibleExamples.vo: FeasibleExamples.v Schedule.vo
	rocq compile FeasibleExamples.v

SchedulableExamples.vo: SchedulableExamples.v Schedule.vo
	rocq compile SchedulableExamples.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
