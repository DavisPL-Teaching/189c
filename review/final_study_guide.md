# Course Review and Study Guide

Review and list of topics for the final!
Please use this guide to help you study.

The final will be cumulative, covering lectures 1, 2, 3, and 4.
See `exam_info` for details on the exam.

(*) are suggested topics to spend extra time on reviewing!

## Lecture 1: Correctness, Specifications, Hypothesis

(Same topics as for the midterm)

Summary, you should know:

- Definition of software correctness
  + Why is it important?

- Specifications
  + writing specifications

- Stronger and weaker specifications (*)
    + examples
    + weaker precondition ==> stronger spec
    + stronger precondition ==> weaker spec

- Types of specifications: functional correctness, full functional correctness,
    safety properties, liveness properties;
    examples and how these are related

- Ways of writing specifications
  + preconditions/postconditions
  + assume and assert
  + how these are related

- Difference between testing & verification

- Advantages and limitations of Hypothesis.

## Lecture 2: Z3 and Satisfiability

(Same topics as for the midterm)

Summary, you should know:

- Proving specifications using Z3

- Satisfiability: definition and application
    + difference between solve/prove

- Three-step process to solve problems with Z3

- Basic data types: Int, Bool, Real

- Limitations of Z3; UNKNOWN and timeouts

## Lecture 3: Advanced Z3

- Why supporting advanced data types is useful
    + String, regex
    + Advanced: Arrays, functions, quantifiers

- Basic regex operators and their meaning: (*)
  union, concat, star, Re, Range, InRe

- Advanced datatypes and troubleshooting
    + What to do if Z3 hangs?
    + What to do if Z3 returns UNKNOWN?

- Z3 internals: the DPLL algorithm for Boolean satisfiability (*)
    + Unit propagation
    + Pure literal elimination
    + Branching

## Lecture 4: Interactive verification in Dafny

- Motivation: why use interactive verification?
    (3 main reasons)
    + tradeoff: effort vs. greater correctness, ability to prove more general specs.
    + ability to compile to other languages

- Abstraction in Dafny
    + method/function distinction; "methods are opaque"
    + unit tests and verification as a black box
    + compile time/runtime distinction
        * preconditions, postconditions, assume/assert get compiled out!
        * dangers of assume

- Strongest postconditions and weakest preconditions (*)
    + SP is on input, output; WP is on input
    + should be able to calculate these for example programs
    + how Dafny works "under the hood"
    + loop-free code

- Loops and loop invariants (*)
    + Why loop invariants are needed
    + Definition of loop invariant: conditions (i)-(iii)
        * application to example programs
    + Intuitive characterization
        (true before start of loop; true after each iteration)
        Intuitive characterization is not the same as (i)-(iii)!

- (Maybe)
    Dafny as a "computationally bounded verifier"; why it needs help;
    troubleshooting

- Advantages and limitations of Dafny.

### General

Best fit tools for the task?
- Here is an example task/program, would Hypothesis, Z3, or Dafny
  be a better fit for this task?

For example:
- The programmer only has limited about of time/effort, what tool should they use?
- The programmer cares about proving the program is safe on ALL inputs, which
  tool should they use?
- The software code needs to be verified but still interact with an existing Python code base,
  which tool should the use?
- Use critical thinking, and rely on what you have learned about the tools in this class!
