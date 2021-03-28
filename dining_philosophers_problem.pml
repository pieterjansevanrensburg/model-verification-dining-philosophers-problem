/*
This program seeks to solve the generalized dining philosophers' problem 
using channels.

It is my implementation of the Resource Hierarchy Solution proposed by 
Edsger W. Dijkstra. 
For more details see: https://en.wikipedia.org/wiki/Dining_philosophers_problem

This solution involves assigning a partial order to the forks and requires that
the forks' availability be checked with respect to said ordering i.e. 
philosophers always checks lower ordered forks first and then higher 
ordered forks.

The partial ordering is simply each fork's position in the array of 
asynchronous channels.

Furthermore, each philosopher is treated as a seperate process that runs in
parallel.
*/

/*
The total number of philophers (and forks) to consider in this problem.
*/
#define number_of_philosophers 5

/*
An array of asynchronous channels, where each channel represents a fork.
The indices of the array indicate the forks' assigned partial ordering.
*/
chan forks[number_of_philosophers] = [1] of {bool};

/*
A process representing a philosopher. It's parameters are as follows:
	lower_index_fork: A reference to a channel which represents the fork 
	adjacent to the philosopher that has the lower array index
	(i.e. lower partial ordering).
	higher_index_fork: A reference to a channel which represents the fork 
	adjacent to the philosopher that has the higher array index
	(i.e. higher partial ordering).
*/
proctype philosopher(chan lower_index_fork; chan higher_index_fork) {
	bool get;
	do 	::	true ->
		/*
		The philosopher tries to get the forks adjacent to them according to 
		their partial ordering (lower index is checked first and then 
		higher index).
		*/
		lower_index_fork?get;
		higher_index_fork?get;
		/*
		Now that the philosopher has both forks adjacent to them, they can
		eat.
		*/
		printf("philosopher %d is eating.", _pid)
		/*
		The philosopher releases the forks as they are done eating.
		*/
		higher_index_fork!get;
		lower_index_fork!get;	
	od
}

init {
	/*
	Make all the forks available to the philosophers.
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
				Note that we assign a partial ordering to the forks 
				based on their positions in the array. 
				
				This is done by simply assigning forks to philosophers in an
				ascending order, except for the final philosopher where the
				first fork in the array is assigned as their lower index fork
				and the higher index fork is the final fork in the array.
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