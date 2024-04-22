"""
Task scheduler

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
