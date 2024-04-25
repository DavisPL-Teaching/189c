"""
Day 11

Announcements

- HW2 due in one week

Recap:

- We used Z3 to build a Sudoku solver

- Z3 is faster and easier than what you could write by hand.

Plan for today:

- Start with the poll

- Use Z3 to build a task scheduler

Questions?

=== Poll ===

https://forms.gle/iVEGnZAneJ2ZRAAWA
https://tinyurl.com/52e7t66z

=== Task scheduler ===

Given a list of tasks, including the time it takes to complete each task and the time until the deadline, can we schedule the tasks in a way that we can complete all of them before the deadline?

=== Example input ===

Task: 1, 3 hours, 12 hours
Task: 2, 2 hours, 10 hours
Task: 3, 1 hour, 5 hours

=== Example output ===

Task 1: [0, 3]
Task 2: [3, 4]
Task 3: [4, 6]
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN
