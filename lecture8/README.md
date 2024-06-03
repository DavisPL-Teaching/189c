# Lecture 8: Safety properties and Rust

The last lecture!
We have a couple of days left to cover
this lecture.

## Day 25

Announcements:

- HW4 due on Monday!

## Recap

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

https://forms.gle/YMSA5yL3J5GFUvP37
https://tinyurl.com/3tva4red

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

Diving in:
- `src/intro.rs`: Introduction to safety properties
- `src/bin`: Rust demos (some cool things you can do with Rust)
- `src/syntax.rs`: Basic Rust syntax

There are also introductory slides in
`Intro_Slides.pdf` and `Ownership_Slides.pdf`,
for reference if needed.
But we will start with the live coding part.

## Day 26

Announcements:

- HW4 due today!
  + Office hours at 4pm

- HW5 (optional extra credit) due Thursday

- I hope you all had a chance to watch the recorded lecture!
  (It also has a poll)

- Makeup option, and all participation polls due Monday, June 10!

Plan:

- Poll

- Recap introduction to Rust

- Cover ownership in Rust (at a high level)

- Next time: course review.

Questions about HW4 or Friday's lecture?

### Poll (June 3)

On Friday, we introduced safety properties.

- A **safety property** is a spec of the following form:
  when the program is run, a "bad" event never occurs.

  I.e.: there is some set of bad states X, and
  when the program is run, a state in X never occurs.

Which of the following are examples of safety properties?
(options in the form below)

https://forms.gle/rBqqug81VYmzSJao7
https://tinyurl.com/4pnhncep

### Poll (June 5)

I will go ahead and post the last poll, for next time (June 5).
Feel free to complete this ahead of time.
We will not look at the results in class today.

https://forms.gle/TsUK9w3SwTEFAt7e7
https://tinyurl.com/27c6yx9z
