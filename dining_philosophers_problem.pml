/*
The total number of philophers (and forks) to consider in this problem.
*/
#define number_of_philosophers 20

chan forks[number_of_philosophers] = [1] of {bool};

proctype philosopher(chan left_fork; chan right_fork) {
	bool get;
	do 	::	true ->
		/*
		The philosopher gets the forks to their left and right.
		*/
		left_fork?get;
		right_fork?get;
		/*
		The philosopher releases the forks to their right and left.
		*/
		right_fork!get;
		left_fork!get;	
	od
}

init {
	int index = 0;
	/*
	Make all the forks available.
	*/
	do	::	index < number_of_philosophers -> forks[index]!true; index++;
		:: 	else -> break;
	od
	
	index = 0;
	/*
	Start all philosopher processes at the same time.
	*/
	atomic{
		do 	:: 	index < number_of_philosophers ->
				if	:: 	index == (number_of_philosophers - 1) ->
						run philosopher(forks[0], forks[index]);
					:: 	else ->
						run philosopher(forks[index], forks[index + 1]);
				fi
				index++;
			:: else -> break;
		od
	}
	
}