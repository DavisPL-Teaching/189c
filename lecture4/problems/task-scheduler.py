"""
Day 11

Announcements

- HW2 due in one week

Recap:

- We used Z3 to build a Sudoku solver

- Z3 is faster and easier than what you could write by hand:

    + about 30 lines of code
    + runs in a tenth of a second

Plan for today:

- Start with the poll

- Use Z3 to build a task scheduler

- This time, we will also focus more on good style (code organization).

Questions?

=== Poll ===

https://forms.gle/iVEGnZAneJ2ZRAAWA
https://tinyurl.com/52e7t66z

=== Task scheduler ===

Given a list of tasks, including the time it takes to complete each task, the time until the deadline, and during what hour(s) it can be completed, can we schedule the tasks in a way that we can complete all of them before the deadline?

=== Example input ===

Time: 8am
Task: 1, 3 hours, 12 hours, 8am to 8pm
Task: 2, 2 hours, 10 hours, 8am to 8pm
Task: 3, 1 hour, 5 hours, 8am to 8pm

=== Example output ===

9am-12pm: Task 1
12pm-1pm: Task 2
1pm-6pm: Task 3
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Let's first consider our three steps:

Remember:

1. What are the variables?
2. What are the constraints?
3. What are the properties we want to check?
"""
