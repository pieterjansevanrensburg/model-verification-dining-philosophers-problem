/*
The total number of philophers (and forks) to consider in this problem.
*/
#define number_of_philosophers 10

/*
A boolean array indicating whether a particular fork has been picked up.
A value of true indicates that it has been picked up. 
Whereas, a value of false indicates that the fork is on the table.
*/
bool forks[number_of_philosophers];

/*
A process representing a philosopher where:
lower_fork_index is the lowest index of a fork (which is next to the
philosopher) in the array.
higher_fork_index is the highest index of a fork (which is next to the
philosopher) in the array.
*/
proctype Philosopher(int lower_fork_index; int higher_fork_index) {
	/*
	Loop forever
	*/
	do :: true ->
		/*
		Philosophers always check if the fork with the lowest index 
		is available first and then the one with the higher index.
		This is my implementation of the Resource Hierarchy Solution 
		proposed by Dijkstra.
		See: https://en.wikipedia.org/wiki/Dining_philosophers_problem
		*/
		Get_Forks:
			/*
			Check for the lower index fork
			*/
			do :: true ->
				atomic {
					if :: forks[lower_fork_index] == false -> 
							forks[lower_fork_index] = true;
							break;
					fi
				}
			od
			/*
			Check for the higher index fork
			*/
			do :: true ->
				atomic {
					if	:: forks[higher_fork_index] == false -> 
							forks[higher_fork_index] = true;
							break;
					fi
				}
			od
		
		/*
		The philosopher has both forks, so here they can eat.
		*/
		Eating:
			printf("Eating");
		
		/*
		Once they have finished eating, they can release both forks in the 
		opposite order in which they were obtained.
		*/
		Release_Forks:
			forks[higher_fork_index] = false;
			forks[lower_fork_index] = false;
	od
}

init {
	/*
	Setup the fork array by setting all values to false. This indicates that
	all forks are placed on the table.
	*/
	int index = 0;
	do 	:: index < number_of_philosophers -> forks[index] = false; index++;
		:: else -> break;
	od
	
	/*
	Kick off all the philosopher processes at the same time.
	Note that the final philosopher's lower fork index is the first fork in the
	array (the same as the 1st philosopher).
	*/
	index = 0;
	atomic{
		do	:: index < number_of_philosophers -> 
				if 	:: index == number_of_philosophers - 1 -> 
						run Philosopher(0, index);		
					:: else ->
						run Philosopher(index, index + 1);
				fi
				index++;
			:: else -> break;
		od
	}
}