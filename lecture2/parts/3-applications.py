"""
ECS 189C

Part 3: Applications of Z3

Satisfiability in Z3 is very powerful.
It can be used for a different paradigm of programming often known as

    "constraint solving" or "logic programming"

We will build a Sudoku solver.

===== Solving problems with Z3 =====

Z3 requires thinking about problems in a very different way!

Z3 process: think about "what" instead of "how":
    - we define the *output* as a set of abstract variables
    - we think about what constraints the output must satisfy
    - (Magic part)
      we pass the constraints to Z3 to solve the problem for us.

(Remember that Z3 integers are not the same as Python integers!)

Steps to solve a problem with Z3:

    1. What are the variables?
    2. What are the constraints?
    3. What are the properties we want to check?

===== Continuing =====

This lecture will continue in

   sudoku.py.

Additional applications in ../extras/.
"""

### ...
### ...
### ...
### ...
### ...
### ...
### ...
### ...
### ...
### ...

"""
=== Discussion questions ===

How would we do this without Z3?

What are the advantages of using Z3?

How is Z3 different from Hypothesis?

What are the drawbacks of using Z3?

=== Follow up ===

- Can we reorganize our code to be better?

- Can we check that there is only one solution?

- Can we generate valid Sudoku puzzles?

- Generalize to an arbitrary N x N board.
(This only works for certain board sizes: 4x4, 9x9, 16x16, etc.)
"""
