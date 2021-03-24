/*
This program seeks to solve the dining philosophers' problem using channels.

It is my implementation of Djikstra's proposed solution of assigning a 
global ordering to the forks and making sure that the philosophers check 
whether forks are available with respect to this ordering.

For more details see: https://en.wikipedia.org/wiki/Dining_philosophers_problem
*/

/*
The total number of philophers (and forks) to consider in this problem.
*/
#define number_of_philosophers 5

/*
An array of asynchronous channels, where each channel represents a fork.
The indices of the array indicate the forks' assigned global ordering.
*/
chan forks[number_of_philosophers] = [1] of {bool};

/*
A process representing a philosopher. It's parameters are as follows:
	lower_index_fork: A reference to a channel which represents the fork 
	adjacent to the philosopher that has the lowest array index.
	higher_index_fork: A reference to a channel which represents the fork 
	adjacent to the philosopher that has the highest array index.
*/
proctype philosopher(chan lower_index_fork; chan higher_index_fork) {
	bool get;
	do 	::	true ->
		/*
		The philosopher gets the forks according to their global ordering
		(lower index is checked first).
		*/
		lower_index_fork?get;
		higher_index_fork?get;
		/*
		The philosopher releases the forks.
		*/
		higher_index_fork!get;
		lower_index_fork!get;	
	od
}

init {
	/*
	Make all the forks available.
	*/
	int index = 0;
	do	::	index < number_of_philosophers -> forks[index]!true; index++;
		:: 	else -> break;
	od
	
	/*
	Start all philosopher processes at the same time.
	*/
	index = 0;
	atomic{
		do 	:: 	index < number_of_philosophers ->
				/*
				Note that we assign a global ordering to the forks 
				based on their positions in the array. 
				
				We also make sure that philosophers always try to obtain 
				the fork adjacent to them which is the lowest in this ordering 
				first and then try to obtain the next one.
				
				This is done by simply assigning forks to philosophers in an
				ascending order, except for the final philosopher when the
				first fork in the array is assigned as their lower index fork.
				*/
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