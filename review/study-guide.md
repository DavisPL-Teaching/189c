# Course Review and Study Guide

## Module 1: Correctness, Specifications, Hypothesis

- Correctness
  + Why is correctness important?
  + Definition of software correctness

- Specifications
  + writing specifications
  + complete specifications

- Writing specifications
  + assume and assert
  + preconditions and postconditions
  + specifications that go beyond assume/assert/precond/postcond:
    "function does not terminate"
    "function is pure"
    "function does not print to stdout"
    etc.


- Methods of validating specifications
  + testing with Hypothesis
  + limitations of Hypothesis

- Facts about specifications:
    + Any (pre, postcondtion) pair is a specification, but not necessarily
      vice versa
    + All safety properties are specifications, but not necessarily vice versa
    + There may be more than one valid spec for the same program!
    + There may be more than one valid way to write pre/postconditions

### Example question formats:

Writing specs:
- Here is a specification and a program, does the program satisfy the spec?
- Which of the following are examples of specifications?
- Here is a program, write
    + A valid specification
        (Note: syntax is not important, but your answer should be conceptually valid)
    + The strongest possible postcondition on the output
        Checks every piece of data in the output

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
    + what definition of correctness Hypothesis uses
        + assume, assert, preconditions, postconditions
    + random generation
    + how assume and assert are handled
- Limitations of Hypothesis
    + Reasons it may not catch a bug
    + Specifications beyond the scope of pre/postconditions
    + What a test passing means in Hypothesis

## Module 2: Z3 and Satisfiability

- Satisfiability
  + what is satisfiability?
  + how does prove() relate to satisfiability?
  + how does solve() relate to satisfiability?

- Steps to solve a problem with Z3
  + declare variables
  + declare constraints
  + ask Z3 to solve or prove the constraints

- Basic idea of some data types and operations supported:
  + Int, Real, Bool
  + Strings, Regex

- Techniques
  + 3 possible outputs (SAT, UNSAT, UNKNOWN)
  + What to do when Z3 fails to solve a problem (returns UNKNOWN or times out)

- Limitations

### Example question formats:

Satisfiability
- Here is a formula, is it satisfiable?
- Here is a formula, is it provable?
    (Note: you don't have to know in what cases Z3 would return unknown!)

Encoding programs using Z3
- Difference between a Z3 variable and a Python variable
- Difference between a Python program and a Z3 program
- How you might encode, for example, an if statement as a Z3 expression
  and what that means

Regular expressions
- Which of the following strings match the regular expression?
- Write a regular expression which encodes the following property
    (I will give reminders for ALL Z3 syntax, your answer doesn't have to
     "compile" but it should be conceptually correct)

Z3:
- Here is some Z3 code, what will happen when it is run?
  (you may assume that it does not timeout or return unknown)
- Which of the following are reasons Z3 may return unknown / timeout?
- Which of the following are limitations of Z3?

## Module 3: Dafny and formal verification

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
    + counterintuitive fact that came up in the Hypothesis module:
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

## Module 4: Rust and Safety Properties

I will only ask you very basic questions about Rust -- see the last two polls.

- What is a safety property?
- Which of the following are safety properties?
- What are the primary safety properties that Rust enforces
- What are advantages/disadvantages of Rust?
- Some motivation:
    + principles of good code
    + user does not have to write the spec
    + Rust is good for speed/performance, low-level systems software, C replacement

You do NOT need to understand the Rust ownership rules, but you should know
the word "ownership" and that it is the fundamental property behind how Rust
works.

## General

Best fit tools for the task?
- Here is an example task/program, would Hypothesis, Z3, or Dafny
  be a better fit for this task?

For example:
- The programmer only has limited about of time/effort, what tool should they use?
- The software code base is huge, what tool should they use?
- The programmer cares about proving the program is safe on ALL inputs, which
  tool should they use?
