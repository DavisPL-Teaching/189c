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

Additional applications can be seen in ../applications
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
=== Recap ===

We've seen that we can solve "puzzle" questions with Z3 by
1) defining variables, 2) defining constraints, 3) passing constraints to Z3
  which magically comes back with a solution.

We've also seen that Z3 supports Booleans and Integers with various operations;
we will see later that Z3 supports several other data types.

It can be useful to create arrays or nested arrays of Z3 variables (like a 2D
or 3D grid of variables)

=== Discussion questions ===

How would we do this without Z3?

    We might hardcode some sort of solution by manually keeping track
    of what each row/column can be

    That won't necessarily always work; we need a "guess and check step"

    Z3 will probably solve the problem faster and with less effort on our
    part.

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

"""
=== Poll ===

Another puzzle we can solve :-)

https://forms.gle/KYgzj9pbQkYVcpqJA

Answers?

- Multiple possible answers - missing information
- Minimum 35 to maximum 51
- Minimum 28 to maximum 51
- Are we assume side picture is for both sides?

Summary of class answers:
A general agreement that max is 51, lots of disagreement
about minimum possible answer.

=== Additional applications ===

Additional applications in lecture2/applications

- 8 queens puzzle: can we put 8 queens on a standard chess board such that no queen attacks any other queen?

- Task scheduler: given a bunch of tasks and allowed time(s), schedule times to complete the tasks

Other problems (not filled out - you are welcome to try to solve them yourself!) in lecture2/other-problems.

"""
