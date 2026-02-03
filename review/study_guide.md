# Course Review and Study Guide

## Covered for Midterm

Midterm will cover Lectures 1 and 2.

### Lecture 1: Correctness, Specifications, Hypothesis

- Correctness
  + Why is correctness important?
  + Definition of software correctness

- Specifications
  + Definition of a specification
  + Methodology of writing specifications:
    1. Write a program, 2. write a specification, 3. use some sort of tool to check
  + Testing vs. verification
  + Given some statements, which of these is
    - a valid spec
    - a true spec for some particular program P

- Stronger and weaker specifications
  + Def. of stronger/weaker
  + Apply the def: here are some specs, which is stronger/weaker than which others
  + False - strongest possible
  + True - weakest possible
  + Any spec S is stronger than itself

- Types of specifications
  + Functional correctness spec
  + Full functional correctness spec
  + preconditions and postconditions
    what these are, able to write examples
    @given can be both used to write preconds
  + specifications that go beyond precond/postcond:
    "function does not terminate"
    "function does not print to stdout"
    "function is pure"
    etc.
    ==> Safety property
      What is a safety property
    ==> Liveness property
      What is a liveness property

- Assume and assert
  + Def. of assume
    assume() can be used to write preconditions
  + Def. of assert
  + Interaction between assume/assert, example:
    assume P; assert P
    is equivalent to
    assume P
  + Preconds/postconds can be written using assume/assert, but not always the
    other way around
  + Hypothesis: can test everything that can be written using assume/assert

- Advantages and limitations of Hypothesis

- Misc.: Facts about specifications:
    + Any (pre, postcondtion) pair is a specification, but not necessarily
      vice versa
    + All safety properties are specifications, but not necessarily vice versa
    + There may be more than one spec that holds for the same program!
    + There may be more than one valid way to write pre/postconditions

### Example question formats:

Writing specs:
- Here is a specification and a program, does the program satisfy the spec?
- Which of the following are examples of specifications?
- Here is a program, write
    + A valid specification
        (Note: syntax is not important, but your answer should be conceptually valid)
    + Full functional correctness:
      The strongest possible postcondition on the output
        Checks every piece of data in the output

Stronger/weaker specs
- Here are some specs spec1 and spec2, is spec1 stronger than spec2?
- What is the strongest possible spec? What is the weakest possible spec?

Types of specs
- What is a safety property?
- Which of the following are safety properties?
- Is the following a functional correctness property?
- Is the following a full functional correctness property?

Pre/postconditions:
- Is the program correct with respect to this pre/postcondition?
- Which of the following preconditions are valid for this program and postcondition?

Assume/assert:
- Is the program correct given the assume() and assert() statements?
- What assume() or assert() statement could be inserted here so that
  the program is correct?

Hypothesis
- Here is a Hypothesis test, what happens when it is run?
- How does Hypothesis work?
    + what specifications Hypothesis can test
        + assume/assert (including preconds/postconds)
    + random generation
    + how assume and assert are handled
- Limitations of Hypothesis
    + Reasons it may not catch a bug
    + Specifications beyond the scope of pre/postconditions
    + What a test passing means in Hypothesis

## Lecture 2: Z3 and Satisfiability

- Proving specifications
  + z3.prove() to prove a spec on all inputs
  + how to encode a precond/postcond spec using Z3:
      prove(z3.Implies(precond, postcond))

- Difference between Z3 and Python
  + Z3 vars/types are different than Python vars/types!
  + Z3 expressions are not evaluated!

- Satisfiability
  + what is a formula?
  + what is satisfiability?
  + how does prove() relate to satisfiability?
  + how does solve() relate to satisfiability?
  + solve() can return 3 possible outputs (SAT, UNSAT, UNKNOWN)
  + prove() can return 3 possible outputs (PROVED, COUNTEREXAMPLE, UNKNOWN)

- Steps to solve a problem with Z3
  + declare variables
  + declare constraints
  + ask Z3 to solve or prove the constraints

- Basic idea of some data types and operations supported:
  + Int, Real, Bool

- We will cover this week:
  (I will update after Thursday)
  + Why Z3 might return UNKNOWN
  + What to do when Z3 fails to solve a problem (returns UNKNOWN or times out)
  + Limitations of Z3

### Example question formats:

Satisfiability
- Here is a formula, is it satisfiable?
- Here is a formula, is it provable?
    (Note: you don't have to know in what cases Z3 would return unknown!)
- If Z3 returns SAT or COUNTEREXAMPLE - it will give an example. Provide
  one such possible example.

Encoding programs using Z3
- Difference between a Z3 variable and a Python variable
- Difference between a Python program and a Z3 program
- How you might encode, for example, an if statement as a Z3 expression
  and what that means
    see HW: update_player_level q

Z3:
- Here is some Z3 code, what will happen when it is run?
  (you may assume that it does not timeout or return unknown)
- Which of the following are reasons Z3 may return unknown / timeout?
- Which of the following are limitations of Z3?

## Post-midterm

### Lecture 3: Dafny and formal verification

What is formal verification?
- Reasons you might want to use formal verification

Abstraction in Dafny and how Dafny works
- What is abstraction in Dafny?
- function/method distinction
- unit tests and what they do
- what gets compiled out of the code?
    + preconditions
    + postconditions
    + assume/assert
- why assume is dangerous
    + assume false anywhere, and then prove and assertion/postcondition
- verification phase vs run/build phase
- Dafny can compile to other languages (e.g., Python)

Dafny advantages/disadvantages

More advanced concepts:

Weakest preconditions and strongest postconditions
- Definition
- What it means to be "weaker" or "stronger"
    + of a precondition or postcondition
        weaker = true for more inputs/outputs
        stronger = true for fewer inputs/outputs
        weakest of ALL conditions? = true
        strongest of ALL conditions? = false
    + of a specification?
        weaker = true for more programs
        stronger = true for fewer programs
    + counterintuitive fact that came up in the Hypothesis Lecture:
        weaker precondition ==> stronger spec
        stronger precondition ==> weaker spec
        weaker postcondition ==> weaker spec
        stronger postcondition ==> stronger spec

Weakest precondition =
    "Describe the (set) of all inputs such that after running the program,
    the postcondition holds"

Strongest postcondition =
    "Describe the (set) of all outputs that are possible after running
     the program on an input satisfying the precondition"

Loop invariants
- Three properties of a loop invariant
- Who writes the loop invariant? (The user)
- Dafny infers weakest preconditions / strongest postconditions
  in order to prove assertions, but does not infer loop invariants

### Example question formats:

Here is a precondition, write the strongest postcondition
    Note: syntax not important here, your answer doesn't need to compile
    but it should be conceptually right
Here is a postcondition, write the weakest precondition
    (Same note as above)

Here are two preconditions/postconditions, which is weaker/stronger?

Here are two specifications, which is weaker/stronger?

Which of the following are potential disadvantages of Dafny?

Which of the following are reasons Dafny may fail to prove a program?

Harder questions (towards the end of the test):
Which of the following is a valid loop invariant?
    Note: I don't expect you to know what Dafny is/isn't able to prove, you
    only have to know conceptually the three properties (i)-(iii) of a loop
    invariant and be able to look at the code to see whether they are satisfied

Write a loop invariant for this piece of code.
    (Same notes as above)

### General

Best fit tools for the task?
- Here is an example task/program, would Hypothesis, Z3, or Dafny
  be a better fit for this task?

For example:
- The programmer only has limited about of time/effort, what tool should they use?
- The software code base is huge, what tool should they use?
- The programmer cares about proving the program is safe on ALL inputs, which
  tool should they use?
