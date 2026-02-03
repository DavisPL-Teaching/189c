"""
ECS 189C

Part 3: Applications of Z3

Satisfiability in Z3 is very powerful.
It can be used for a different paradigm of programming often known as

    "constraint solving" or "logic programming"

Idea:

    Instead of telling the computer exactly what to do,
    tell it the constraints that a solution should satisfy,
    and let the computer come up with the solution.

We will build a Sudoku solver.

===== Poll =====

Which of the following is a true statement about how prove() or z3.prove() works?
(Select all that apply)

A. prove(spec) tries to prove the spec holds on at least one input
B. prove(spec) returns PROVED, COUNTEREXAMPLE, or UNKNOWN
C. prove(z3.Implies(precond, postcond)) can be used to prove a program specification
D. prove(spec) is internally the same as solve(spec or not(spec))
E. prove(spec) is internally the same as solve(not(spec))
F. prove(spec) does not relate to solve() internally

https://forms.gle/uaLq4Kd1viZnmjFw7

===== Solving problems with Z3 =====

Z3 requires thinking about problems in a very different way!

    Think about "what" instead of "how"!

Steps to solve a problem with Z3:

    1. What are the variables?

        Define the *output* as a set of abstract variables (z3.Int, z3.Bool etc)

    2. What are the constraints?

        We think about the constraints the output should satisfy

    3. What are the properties we want to check?

        (Magic part:) Pass the constraints to Z3 to solve the problem for us!

        Typically, single call to solve/prove at the end.

Remember:
- Z3 datatypes are not the same as Python types!
- Z3 expressions like ==, >, and/or etc. are not evaluated.

===== Continuing =====

This lecture will continue in

   sudoku.py.

Additional applications can be seen in ../extras
and additional problems (not solved) in ../other-problems.

"""

print("Lecture continues in sudoku.py")

# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .

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
