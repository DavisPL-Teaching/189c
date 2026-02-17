"""
Lecture 3, Part 3:
Z3 Internals: The DPLL algorithm.

===== Z3 internals =====

So how does Z3 work anyway?
Z3 is known as an "SMT solver": Satisfiability Modulo Theories.

- We know what "satisfiability" means

  We saw this in a previous lecture

Example:
Boolean satisfiability:

(p or q or r) and (~p or ~q or ~s) and (s)

We said it's "satisfiable" if there exists some values of the input
variables such that the formula is true.

The traditional problem of satisfiability, or SAT, is with boolean
variables -- if you've taken a CS theory class, you may have seen
that this is a famous example of an NP-hard problem. What that maens
is roughly that it's impossible to solve efficiently in general, in
general you would need exponential time to solve the problem.

A traditional Satisfiability solver (SAT solver) just deals with boolean
variables. So the second part is:

- The "theories" part is the fact that it can handle different data types:
  each data type, like integers, Reals, and Strings, comes with its own
  *theory* of how to process constraints on that data type.

Example:
  x = z3.Int("x")
  x < 2 and x > 2

We have the exact same thing as before, but we've replaced
p, q, r, and s with facts about our integer data type:
"x < 2" and "x > 2" are the new p, q, r, s:
Z3 will assign boolean variables:

  p = "x < 2"
  q = "x > 2"

Then it will apply a solver for boolean satisfiability.

How do we solve boolean satisfiability?

  (p or q or r) and (~p or ~q or ~s) and (s)

Simplest idea: try values of the variables.
First try p = True, then try p = False.

But that's not very clever.
Anything we could do better?
- Suggestion to: look at s!
- s has to be true! So let's just plug in s = True.

  (p or q or r) and (~p or ~q or False) and (True)

simplifies to:
  (p or q or r) and (~p or ~q)

What else should we look at?
- Suggestion 2: look at r!
- Just pick r = True, because if it's satisfiable, it might
  as well be satisfiable with r = True.

  (p or q or True) and (~p or ~q)
  True and (~p or ~q)
  ~p or ~q

Repeat.
--> set p to False
  True or ~q
  True
and we're done. Return satisfiable.

That's the rough idea behind basic satisfiability solving (SAT)

Remember that Z3 works with arbitrary data types.
There's one last step! Write out what we have:
  s = True
  r = True
  p = False
And we use a theory-specific solver to determine
whether these are a satisfiable set of formulas for the particular
data type we are using such as z3.Int.
E.g.: if
  s = x > 0
  r = x < 0
then we would find that this is not satisfiable, and we have to go
back and try again.

Discussion:
we just solved boolean satisfiability, suppoesdly an NP-complete
problem, extremely efficiently!
How is that possible?

The entire philosophy behind Z3: satisfiability is only NP complete
in the **worst case.**
In average cases, or practical examples that come up in the real world,
it's probably not too computationally difficult to solve them.

(Not on the exam)

There are two algorithms,
we will not go over them in detail:
- DPLL: Davis-Putnam-Logemann-Loveland
  https://en.wikipedia.org/wiki/DPLL_algorithm
  That's the one that we just showed above

- CDCL: Conflict-Driven Clause Learning
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
  Optimized/better version

===== Z3 Review =====

Proofs and satisfiability

We saw that:
Using the problem of satisfiability, we can:
- solve() constraints
- and we can prove() specifications.

We should now be comfortable with using Z3 to set up a problem:
1. Declare variables
2. Declare constraints
3. Ask Z3 to solve the constraints

Z3 has two "modes" that we have used: solve() and prove().
- solve(): find a solution for *at least one* input
- prove(): prove that the statement is true *for all* inputs

How do program specifications relate to Z3?
(Problem 1B on HW2 is about this)

    inputs = ... # Z3 variables
    output = call_program(inputs)
    precondition = ...
    postcondition = ...
    spec = z3.Implies(precondition, postcondition)
    prove(spec)

We can also use Z3 more like Hypothesis to generate example inputs.
How?

    inputs = ... # Z3 variables
    precondition = ...
    example = get_solution(precondition)

^^ This is basically how Hypothesis works!

We saw that the main limitation of Hypothesis was?

- It can find a bug, but it can never prove that there are no bugs!

Main limitations of Z3?
(There are two)

1. We have to rewrite the program in Z3
2. Z3 might hang or return unknown

And that's where we are going next!

With general program verification frameworks!

The program and the proof will both be written in the same
framework.

===== Mid quarter review =====

This concludes the first half of the course!
See the file `mid_quarter_review.md`.
"""
