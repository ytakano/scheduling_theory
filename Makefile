Base.vo: Base.v
	rocq compile Base.v

Schedule.vo: Schedule.v Base.vo
	rocq compile Schedule.v

PeriodicTasks.vo: PeriodicTasks.v Base.vo
	rocq compile PeriodicTasks.v

example_feasible.vo: example_feasible.v Schedule.vo
	rocq compile example_feasible.v

clean:
	rm -f *.vo *.glob *.vok *.vos *.aux
