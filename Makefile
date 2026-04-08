all: EDF.vo example_feasible.vo

Base.vo: Base.v
	rocq compile Base.v

Schedule.vo: Schedule.v Base.vo
	rocq compile Schedule.v

PeriodicTasks.vo: PeriodicTasks.v Base.vo
	rocq compile PeriodicTasks.v

UniSchedulerInterface.vo: UniSchedulerInterface.v Schedule.vo Base.vo
	rocq compile UniSchedulerInterface.v

EDF.vo: EDF.v Schedule.vo Base.vo UniSchedulerInterface.vo
	rocq compile EDF.v

example_feasible.vo: example_feasible.v Schedule.vo
	rocq compile example_feasible.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
