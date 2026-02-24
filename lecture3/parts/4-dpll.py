"""
Lecture 3, Part 4:
Z3 Internals: The DPLL algorithm.

The way we've used Z3:
a "magic black box"

  Input some formulas =======> out comes answer
                               PROVED or COUNTEREXAMPLE (or UNKNOWN)
                               SAT or UNSAT (or UNKNOWN)

  (Kind of like an all-powerful all-knowing "oracle")

  But we've seen that the oracle is not perfect,
  and can't always solve our problem

  Let's break open the magic box - how does this work
  on the inside?

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

(Quiz: is this satisfiable?)

Yes:
    p true, q false, s true
    (works! So it's satisfiable)

The traditional problem of satisfiability, or SAT, is with boolean
variables -- if you've taken a CS theory class, you may have seen
that this is a famous example of an NP-complete or NP-hard problem.
What that means
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

Then I just have:

  p and q

  we infer some additional constraint from the theory such as

  "not (p and q)"

  due to the fact that no integer can be both > and < the same integer,
  then resulting in UNSAT.

Then it will apply a solver for boolean satisfiability.

For the rest of this lecture I will just talk about
Booleans.

How do we solve boolean satisfiability?

  (p or q or r) and (~p or ~q or ~s) and (s)

  ^^^^ written as a conjunction "and" of disjunctions "or"

  called: conjunctive normal form:
    "and" of a bunch of "ors"

  First step, we'll assume the formula is written in this form.

How might we come up with an algorithm here?

  Observation 1: start by marking s true
    -- because its in a clause of its own.

  More generally: if any of our conjuncts (anded things)
  has only one variable, we can mark that variable
  true/false. (s => mark true, ~s => mark false).

  Result after marking s = true:

    (p or q or r) and (~p or ~q)

  No more clauses left with a single var :-(

  Next step? Suggestions:

  - Reduce the terms by doing demorgans laws:

      (A or B) and C ==> (A and C) or (B and C)

  - Try different values of p or q...

  - Look at the variable r ...

    We can just set it to true - because it only appears
    once, so it "might as well" be true.

      More general version:

        If r (or any other variable) only appears
        in a strictly positive form (r)
        or in a strictly negative form (~r),
        set it to true or false, respectively.

  After setting r = true:

    (p or q or r) and (~p or ~q)

    (p or q or true) and (~p or ~q)
    ^^^^^^^^^^^^^^^^ true

    true and (~p or ~q)

    (~p or ~q)

    Now?

      ~p only appears as ~p, so set p = false


    (true or ~q)
    true

    return SAT

    give an example:
    read off the choices we made:
      s = true
      r = true
      p = false
      q = <return anything>

.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.
.

----- SKIP -----

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

----- SKIP -----

and we're done!
We've solved the satisfiability problem

  (supposedly an expentially hard NP hard problem)

without ever resorting to "try all possibilities"

That's the rough idea behind basic satisfiability solving (SAT).

This is the idea of the DPLL algorithm:
Davis-Putnam-Logemann-Loveland

Pseudocode:

    Assume that the input is in conjunctive normal form

      clause1 AND clause2 AND clause3 AND ...

    each clause is an OR of some variables x or ~x (NOT x).

    Loop:

        1. Unit Propagation:

            If we see a clause that has only a single variable,
            mark that variable true or false.

            (in our example: variable s)

        2. Pure Literal Elimination:

            If we see a variable that appears only
            in one form ("pure" form) - x only, or ~x only,
            mark all instances of that true or false
            (respectively)

            (in our example: variables r, ~p)

        3. Branching:

          If both 1 and 2 fail, pick a variable x,
          and guess x = true or x = false.
          If one fails, go back and try the other one.

            (i.e., try all possibilities)

            (did not come up in our example.)

        If any clause becomes just FALSE, backtrack and continue

        If all clauses are gone (no clauses left to satisfy), return SAT

    // After loop finishes - we've tried all possibilities,
    // and none of them work
    return UNSAT

===== Generalizing to arbitrary data types =====

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

===== Other algorithms for satisfiability =====

(Not on the exam)

There are two algorithms,

- DPLL: Davis-Putnam-Logemann-Loveland
  https://en.wikipedia.org/wiki/DPLL_algorithm
  That's the one that we just showed above

- CDCL: Conflict-Driven Clause Learning
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
  Optimized/better version

===== Discussion =====

we just solved boolean satisfiability, supposedly an NP-complete
problem, extremely efficiently!
How is that possible?

The entire philosophy behind Z3: satisfiability is only NP complete
in the **worst case.**
In average cases, or practical examples that come up in the real world,
it's probably not too computationally difficult to solve them.

===== Z3 Quick Review =====

Proofs and satisfiability:

Z3 is based on the satisfiability problem.
It can be used to solve() constraints and to prove() specifications.

We should now be comfortable with using Z3 to set up a problem:
1. Declare variables
2. Declare constraints
3. Ask Z3 to solve (or prove) the constraints

Comparison with Hypothesis?
We can also use Z3 more like Hypothesis to generate example inputs.
How?

    inputs = ... # Z3 variables
    precondition = ...
    example = get_solution(precondition)

^^ If you squint your eyes and ignore the details, this is basically how Hypothesis works!

We saw that the main limitation of Hypothesis was?

- It can find a bug, but it can never prove that there are no bugs!

Main limitations of Z3? (see Lecture 2, part 4, conclusions)

L1. We have to rewrite the program in Z3
L2. Z3 might hang or return unknown

And that's where we are going next,
with general program verification frameworks!

Z3 is "push button verification" - we push a button, and Z3 solves the problem for us!
Without any human input. We will have to give up the idea of "push button verification" for the
rest of the course. This will take two forms:

L1. The program, the spec, and the proof will all be written in the same framework.

L2. The framework will allow us to help out by writing the proof
ourselves, so that we don't need to rely on automated solvers.
(This sounds like more work - it is! But it also means that we can never get stuck.)
"""
