# Lecture 8: Safety properties and Rust

The last lecture!

This class has been about software correctness. We've learned
that:
- In order to consider correctness -- we need a specification.
- Specifications come in many forms; the primary type we have
  considered uses a precondition and a postcondition.
- There are different methods to check that a program
  is correct with respect to a specification:
  + random testing:
    randomly generate inputs to see if it works (Hypothesis)
  + satisfiability checking:
    write a formal model of the program and prove that it works,
    or find a counterexample (Z3)
  + formal verification:
    invest human effort to construct a formal, rigorous, mathematical
    proof that the program works, using the help of a
    formal verification language or "proof assistant" (Dafny).

What do all these techniques have in common?

They all require the user to write a specification!

### Poll

TODO

### Alternative approaches?

Here's a provocative question: are there some properties of programs
that we should want to hold of *all* programs, no matter how the
program is written? So that if a program violates that property,
no matter what the user intended, it's probably wrong and at the
very least discouraged?

If there are such properties -- such "rules" of good code --
then we don't need the user to
write the specification: instead, the programming language itself
can enforce the rules and complain if you violate them.
That's the main idea behind strongly typed languages in general
and behind Rust in particular.

## Safety properties

So far, specs we have considered come in the following forms:

- Pre/postconditions
- Assume and assert statements
- Termination (a bit -- not a lot of this)

But these are actually quite limited. There are many properties
that go beyond assume and assert.
For example:

- The program never access invalid memory
- The program does not connect to the internet
- The program never constructs an invalid value of type `bool`
  (i.e., a boolean that is not 0 or 1)

Important exercise: why are these properties not specifiable as
pre/postconditions or using assert statements?

### What is a safety property?

All of the are examples of safety properties.

Recall: a spec is a true or false property about a program.

- A **safety property** is a spec of the following form:
  when the program is run, a bad thing never occurs.

What is a "bad thing"? It can be anything. The point of a safety
property is that there are some set of bad things that could occur,
say $X$, and the safety property says that $X$ never happens.

Not just at the time the program has input or produces output --
at any point during the execution of the program!

### Safety properties we are interested in

We will focus on the following two important classes of safety
properties:

- **Type safety:** A value of a type T is always a valid value of
  that type, never some other value.
  Example: bool, always 0 or 1 (not some other int)
  example: int, always a value betweeen -2^31 and 2^31 - 1
  Example: Vec<int>, always consists of a length and a pointer
    to some values of type int

- **Memory safety:** Roughly speaking: memory accesses are always
  valid. This includes:
    - the program only reads from valid, properly allocated memory
    - the program only writes to valid, properly allocated memory
    - the program does not free the same memory twice
    - the program does not crash with a segmentation fault
  Also sometimes included:
    - if memory is allocated, then that memory is later freed
      (no memory leaks)

One other that is important for Rust, but which we will not discuss
is related to concurrent programs:

- **Data race freedom:** It never happens that two threads try
  to write to the same memory location at the same time.
  (Or, one thread tries to write and one thread tries to read.)

### What is Rust?

Rust is a very fast language (performance comparable to that of C)
that enforces type safety, memory safety, and data race freedom.

That means: if you write any program in Rust
    (excluding using some explicitly unsafe features, like the
     `unsafe` keyword),
it is guaranteed to satisfy these safety properties.

### Other specifications?

Fun fact: There are even more advanced properties than the above,
like:

- If the program is run twice on different inputs, the running time
  is the same
  (constant-time programming, very important for security reasons)

But we won't get into more advanced properties like these in this
class.
