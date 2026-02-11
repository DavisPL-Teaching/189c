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
        [
            z3.Bool(f"box{h}{i}{j}") for j in range(7)
        ]
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
# Implicit assumption - gravity applies, so there should
# be a box at height 0.
for i in range(3):
    for j in range(7):
        constraints.append(z3_grid[0][i][j])

# Side view
for h in range(3):
    for j in range(7):
        if (j, h) in [(4, 2), (5, 2), (6, 1), (6, 2)]:
            # L-shape is NOT filled
            for i in range(3):
                constraints.append(z3.Not(z3_grid[h][i][j]))
        else:
            # remainder (outside L shape) IS filled
            # use z3.Or
            constraints.append(z3.Or([
                z3_grid[h][i][j] for i in range(3)
            ]))

# Back view
for h in range(3):
    for i in range(3):
        # using z3.Or again
        constraints.append(z3.Or([
            z3_grid[h][i][j] for j in range(7)
        ]))

# We said we were assuming gravity ...
# We haven't fully encoded gravity

# *** Gravity constraint ***
for h in range(1, 3):
    for i in range(3):
        for j in range(7):
            constraints.append(z3.Implies(z3_grid[h][i][j], z3_grid[h - 1][i][j]))

"""
Step 3: Pass the constraints to Z3

Remains: ... we need total number of cubes

z3.Sum ?

How to convert Booleans to integers?

    z3.If(b, 1, 0)
"""

total_cubes = 0
for h in range(3):
    for i in range(3):
        for j in range(7):
            total_cubes += z3.If(z3_grid[h][i][j], 1, 0)

spec = z3.And(constraints)

# Helper function to print solution
def pretty_print_solution(constr):
    model = get_solution(z3.And(spec, constr))
    if model is None:
        print("No solution")
        return
    print("Height: 0         1         2")
    for i in range(3):
        box_row = "     "
        for h in range(3):
            box_row += "   "
            for j in range(7):
                box = model[z3_grid[h][i][j]]
                box_row += ('#' if box else '.')
        print(box_row)

# maximum is 51:
pretty_print_solution(total_cubes > 51)

# Unsat
pretty_print_solution(total_cubes < 31)

# Sat
pretty_print_solution(total_cubes == 31)

"""
i.e. for this particular set of (faulty) assumptions
the minimum number of cubes happens to be 31.

Exercise: try out different assumptions, and see how many
answers you can get for the minimum possible number of cubes.
"""
