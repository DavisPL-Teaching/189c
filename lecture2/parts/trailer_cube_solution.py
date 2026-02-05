"""
ECS 189C

Trailer cube puzzle

Let's use Z3 to find out & resolve this question.

=== Trailer cube puzzle ===

How many cubes are in the trailer?

A small spoiler:
The answer may depend on which assumptions are made.
"""

"""
Imports and helper functions
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Step 1: Define variables

An integer x?
"""

# answer = z3.Int("x")
# solve(answer == 51) # problem?

# go based on position?
# Make a bunch of Boolean variables for whether or not a box is in a particular
# location

# Nested arrays are once again useful
# 3 x 3 x 7
# height, row, column

z3_grid = [
    [
        [z3.Bool(f"box{h}{i}{j}") for j in range(7)]
        for i in range(3)
    ]
    for h in range(3)
]

"""
Step 2: Define our constraints.

Top view:
- Anything at height 0 is filled?

  ^^^ implicitly making an assumption!

      (gravity is present)

Side view:
- Anything in the L shape is not filled

Back view:
- At least one box in every (depth, row) position such that the back view
  is filled.
"""

constraints = []

# Top view
for i in range(3):
    for j in range(7):
        constraints.append(z3_grid[0][i][j])

# Side view
for (j, d) in [(4, 2), (5, 2), (6, 1), (6, 2)]:
    for i in range(3):
        constraints.append(z3.Not(z3_grid[d][i][j]))

# We've said that the L-shape is NOT filled;
# We also need that the remainder of the side view is filled.
# TODO

# Back view
# TODO

"""
Step 3: Pass the constraints to Z3
"""
