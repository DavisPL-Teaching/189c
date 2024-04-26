"""
Day 11

(to follow along: 189C/lecture4/task-scheduler.py)

Announcements

- HW2 due in one week

- HW1 grading: comments will show up in your GitHub pull request;
    please hold off on regrade requests until further instructions
    are posted on Piazza.

Recap:

- We used Z3 to build a Sudoku solver

- Z3 is likely faster and easier than what you could write by hand:

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

Given a list of tasks, including the time it takes to complete each task, the time until the deadline, and during what hour(s) it can be completed, is it possible to schedule the tasks in a way that we can complete all of them before the deadline?
If so, what's an example schedule?

=== Example input ===

Time: 8am
Task: 1, 3 hours, 12 hours, 8am to 8pm
Task: 2, 2 hours, 10 hours, 8am to 8pm
Task: 3, 1 hour, 5 hours, 8am to 8pm

=== Example output ===

8am-9am: Task 3
9am-11am: Task 2
11am-2pm: Task 1

=== Design considerations ===

Let's assume that tasks are always scheduled in 1-hour blocks.
(1 hour is the smallest time unit here)

Will it always be possible?
No.

Is it possible there is space where we are doing nothing?
Yes

Do we always do one task in one contiguous block?
(For simplicity, let's say no for now.
but we could add it if we wanted to in a future update to our app.)
You have to do each task in one sitting.

What are we prioritizing?
What are we optimizing for here?
(For simplicity, let's set aside this q for now,
but we could add it if we wanted to in a future update to our app.)

"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Let's first consider our three steps:

Remember: Think about the output, not the input.

1. What are the variables?
2. What are the constraints?
3. What are the properties we want to check?

1. What are the variables?

The tasks and the information about them
- how long they take, when you can do them, when they are due
(^ this one is input, not output)

Make a variable for each one hour chunk
^ 2nded

Make a variable for the first task that gets completed,
the second one, and so on.

a boolean?

Mapping of tasks to time that they are completed at?

For each task, what time should we start that task?
^
Let's go with the last one

Let's make a Python class for our scheduler.

API we have in mind:

    scheduler = Scheduler(start_time)
    scheduler.add_task(...)
    scheduler.add_task(...)
    scheduler.get_solution() # print solution

"""

class Scheduler:
    def __init__(self, start_time):
        self.start_time = start_time

        self.task_names = []
        self.task_durations = []
        self.task_deadlines = []
        self.task_available_hours = []

        self.schedule = []

    def add_task(
        self,
        task_name,
        task_duration,
        task_deadline,
        available_hours_start, # between 0 and 24
        available_hours_end, # between 0 and 24
    ):
        n = len(self.tasks) + 1
        self.task_names.append(task_name)
        self.task_durations.append(task_duration)
        self.task_deadlines.append(task_deadline)
        self.task_available_hours.append(
            (available_hours_start, available_hours_end)
        )
        self.schedule.append(z3.Int(f"task{n}"))

        # TODO next: add in the constraints here.

############### Where we left off for day 11 ###############
