"""
ECS 189C

Sudoku solver

(For part 3: Z3 Applications)

=== Sudoku ===

A Sudoku puzzle is a 9x9 grid of numbers, where each row, column, and 3x3 box contains all of the numbers from 1 to 9.

+-------+-------+-------+
| 5 3   |   7   |       |
| 6     | 1 9 5 |       |
|   9 8 |       |   6   |
+-------+-------+-------+
|  ...  |  ...  |  ...  |
|       |       |       |
|       |       |       |
+-------+-------+-------+
|       |       |       |
|       |       |       |
|       |       |       |
+-------+-------+-------+

We are given as input a partially filled grid, where some of the cells
are empty (indicated by 0). Our goal is to fill in the empty cells
with the numbers from 1 to 9 to solve the puzzle.

=== Example input ===

[[5, 3, 0, 0, 7, 0, 0, 0, 0],
 [6, 0, 0, 1, 9, 5, 0, 0, 0],
 [0, 9, 8, 0, 0, 0, 0, 6, 0],
 [8, 0, 0, 0, 6, 0, 0, 0, 3],
 [4, 0, 0, 8, 0, 3, 0, 0, 1],
 [7, 0, 0, 0, 2, 0, 0, 0, 6],
 [0, 6, 0, 0, 0, 0, 2, 8, 0],
 [0, 0, 0, 4, 1, 9, 0, 0, 5],
 [0, 0, 0, 0, 8, 0, 0, 7, 9]]

=== Example output ===

[[5, 3, 4, 6, 7, 8, 9, 1, 2],
 [6, 7, 2, 1, 9, 5, 3, 4, 8],
 [1, 9, 8, 3, 4, 2, 5, 6, 7],
 [8, 5, 9, 7, 6, 1, 4, 2, 3],
 [4, 2, 6, 8, 5, 3, 7, 9, 1],
 [7, 1, 3, 9, 2, 4, 8, 5, 6],
 [9, 6, 1, 5, 3, 7, 2, 8, 4],
 [2, 8, 7, 4, 1, 9, 6, 3, 5],
 [3, 4, 5, 2, 8, 6, 1, 7, 9]]
"""

"""
Step 0: let's import z3 and our helper functions.
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Step 1: Define variables
"""

def get_input():
    # Placeholder: get input from the user
    return [[5, 3, 0, 0, 7, 0, 0, 0, 0],
            [6, 0, 0, 1, 9, 5, 0, 0, 0],
            [0, 9, 8, 0, 0, 0, 0, 6, 0],
            [8, 0, 0, 0, 6, 0, 0, 0, 3],
            [4, 0, 0, 8, 0, 3, 0, 0, 1],
            [7, 0, 0, 0, 2, 0, 0, 0, 6],
            [0, 6, 0, 0, 0, 0, 2, 8, 0],
            [0, 0, 0, 4, 1, 9, 0, 0, 5],
            [0, 0, 0, 0, 8, 0, 0, 7, 9]]

input_grid = get_input()

# Need to define Z3 vars
# what should I do here?

# Suggestion: use a double for loop to define a variable
# - for each cell of the grid?
# - for each zero in the grid?

z3_grid = [[None for i in range(9)] for j in range(9)]
for i in range(9):
    for j in range(9):
        z3_grid[i][j] = z3.Int(f"a{i}{j}")
                                # ^^^ f-string
                                # ^^ vars will be: a00, a01, a02, ...
                                # a + str(i) + str(j)

print(z3_grid)

# 9x9 = 81 different variables

"""
Step 2: Define our constraints.

What constraints do we have?

- If a particular number exists at any row i, col j,
  no other number in that row or column can be the same number.

- Every value should be 1 through 9

- Each 3x3 subgrid "box" should have the numbers 1-9

- If a value in our input grid is nonzero, then the output
  grid should be equal to input grid

- Grid should be 9x9?

    (We don't need bc we hardcoded 9x9 vars)

- Uniqueness of solution?

    We could check this - for now, ask Z3 to give us one solution.
"""

# constraints list
constraints = []

# - Every value should be 1 through 9

for i in range(9):
    for j in range(9):
        constraints.append(z3_grid[i][j] >= 1)
        constraints.append(z3_grid[i][j] <= 9)

# - If a particular number exists at any row i, col j,
#   no other number in that row or column can be the same number.
#
#   + In each row, every pair of numbers in that row is different
#   + In each col, every pair of numbers in that col is different

# Helper function - returns whether a list of 9 Z3 vars is all unique.

# Make a list of vars in a row?

# Rows
for i in range(9):
    # Go through the row - for each spec that already has a defined number...
    # Make two nested loops - go through every pair of numbers and add
    # the constraint that they're not equal
    for j1 in range(9):
        for j2 in range(j1 + 1, 9):
            constraints.append(z3_grid[i][j1] != z3_grid[i][j2])

# Other solutions
# Sort the values in the row as a set, compare with 1..9?
#   - doesn't work bc these are Z3 vars, not Python ints
# Sum the values in the row?
#   - maybe with some sort of fancy bit shift operation?

# columns
for j in range(9):
    for i1 in range(9):
        for i2 in range(i1 + 1, 9):
            constraints.append(z3_grid[i1][j] != z3_grid[i2][j])

# - Each 3x3 subgrid "box" should have the numbers 1-9

# Plan:
# - Iterate over all boxes
# - Iterate over cells in the box

def distinct_nine(l):
    # Input: a list of 9 variables
    # output: a Z3 formula that states they are all distinct
    constraints = []
    for i1 in range(9):
        for i2 in range(i1+1, 9):
            constraints.append(l[i1] != l[i2])
    return z3.And(constraints)

for box_i in range(3):
    for box_j in range(3):
        # box number box_i, box_j
        # rows in the box:
        box = []
        for i in range(box_i * 3, box_i * 3 + 3):
            # cols in the box:
            for j in range(box_j * 3, box_j * 3 + 3):
                box.append(z3_grid[i][j])
        constraints.append(distinct_nine(box))

# Do we need:
# - Each of the values 1-9 appear in each row, and in each col, and in each box?

# for digit in range(9):
#     for i in range(9):
#         possibilities = []
#         for j in range(9):
#             possibilities.append(z3_grid[i][j] == digit)
#         one_of_the_row_is_digit = z3.Or(possibilities)
#         constraints.append(one_of_the_row_is_digit)

# ^^^
# No, not needed - because we checked that each entry is 1-9,
# and that each pair of entries (for example, in each row) is distinct
# that implies that each number 1-9 will necessarily occur.

# - If a value in our input grid is nonzero, then the output
#   grid should be equal to input grid

# replace entries in the input grid into Z3 grid?
# enumerate each element of solution, if the same position in the input
# is not zero, the output should equal the input.

for i in range(9):
    for j in range(9):
        if input_grid[i][j] != 0:
            constraints.append(z3_grid[i][j] == input_grid[i][j])

"""
Step 3:
    Pass to Z3 to get solution
"""

# result = solve(z3.And(constraints))

# print(result)

# more helpful output?

result = get_solution(z3.And(constraints))

solution = [
    [
        result[z3_grid[i][j]]
        for j in range(9)
    ]
    for i in range(9)
]

print(solution)

"""
What happened?

Z3 solved the puzzle

Q: Does Z3 use brute force?

A: No, if you were to consider all values 1-9 in each input, you would get
   some astronomically large number of possibilities

   Z3 is smarter than that.

Short answer: magic :-)

Longer answer: Roughly speaking, Z3 looks at constraints that need to be satisfied
and does a more intelligent search, ruling out branches or possibilities
that can't work.
"""

# We could also spend some effort to clean up our code and make
# the solution work for all input grids (rather than a hardcoded one),
# and to pretty print the output,
# and we could also check that the solution is unique.
# I will leave this as an exercise.

## Some extra code (uncomment if you like)

# Pretty print the grid
# for i in range(9):
#     print(" ".join([str(output_grid[i][j]) for j in range(9)]))

# Is the answer correct?
# assert solution == [
#  [5, 3, 4, 6, 7, 8, 9, 1, 2],
#  [6, 7, 2, 1, 9, 5, 3, 4, 8],
#  [1, 9, 8, 3, 4, 2, 5, 6, 7],
#  [8, 5, 9, 7, 6, 1, 4, 2, 3],
#  [4, 2, 6, 8, 5, 3, 7, 9, 1],
#  [7, 1, 3, 9, 2, 4, 8, 5, 6],
#  [9, 6, 1, 5, 3, 7, 2, 8, 4],
#  [2, 8, 7, 4, 1, 9, 6, 3, 5],
#  [3, 4, 5, 2, 8, 6, 1, 7, 9]]
