# Lecture 2: More complex specifications

## Announcements

- HW0 is due today 11:59pm

- HW1 is released! Due Wednesday, April 17.

## Recap

We've talked about components of correctness:
- A program
- A specification
- Preconditions

We've learned syntax for writing specifications in Hypothesis.

The technical name for Hypothesis is that it's a "property-based testing tool" (PBT). Why?

## Clearing up: Specifications

I've been using the word "specification" (spec) a lot.
What does it mean?
**It's just a requirement that a program should satisfy.**
Some programs satisfy the spec, others don't.
Like a blueprint for a house, or a manual for making

Some philosophy here: remember the car example from lecture 0?
What does it mean for a program to be "correct"?
Our answer is that it *can't* mean anything, unless there is some
definition of what it *means* to be correct.
That definition is a specification.

## Plan

- Writing preconditions
- Revisiting our definition of correctness

- Talk about preconditions
- Do a programming exercise
