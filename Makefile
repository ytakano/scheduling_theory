all: EDF.vo FeasibleExamples.vo SchedulableExamples.vo Partitioned.vo FIFO.vo FIFOExamples.vo PeriodicTasks.vo DispatchLemmas.vo DispatchClassicalLemmas.vo DispatchSchedulerBridge.vo

Base.vo: Base.v
	rocq compile Base.v

ScheduleModel.vo: ScheduleModel.v Base.vo
	rocq compile ScheduleModel.v

SchedulerInterface.vo: SchedulerInterface.v ScheduleModel.vo
	rocq compile SchedulerInterface.v

PeriodicTasks.vo: PeriodicTasks.v Base.vo
	rocq compile PeriodicTasks.v

DispatchInterface.vo: DispatchInterface.v ScheduleModel.vo SchedulerInterface.vo Base.vo
	rocq compile DispatchInterface.v

DispatchLemmas.vo: DispatchLemmas.v DispatchInterface.vo
	rocq compile DispatchLemmas.v

DispatchClassicalLemmas.vo: DispatchClassicalLemmas.v DispatchLemmas.vo
	rocq compile DispatchClassicalLemmas.v

DispatchSchedulerBridge.vo: DispatchSchedulerBridge.v DispatchInterface.vo SchedulerInterface.vo
	rocq compile DispatchSchedulerBridge.v

EDF.vo: EDF.v ScheduleModel.vo Base.vo SchedulerInterface.vo DispatchInterface.vo DispatchSchedulerBridge.vo
	rocq compile EDF.v

FIFO.vo: FIFO.v ScheduleModel.vo Base.vo SchedulerInterface.vo DispatchInterface.vo DispatchSchedulerBridge.vo
	rocq compile FIFO.v

FIFOExamples.vo: FIFOExamples.v FIFO.vo ScheduleModel.vo Base.vo
	rocq compile FIFOExamples.v

Partitioned.vo: Partitioned.v ScheduleModel.vo Base.vo SchedulerInterface.vo DispatchInterface.vo
	rocq compile Partitioned.v

FeasibleExamples.vo: FeasibleExamples.v ScheduleModel.vo
	rocq compile FeasibleExamples.v

SchedulableExamples.vo: SchedulableExamples.v ScheduleModel.vo SchedulerInterface.vo FIFO.vo Partitioned.vo
	rocq compile SchedulableExamples.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
