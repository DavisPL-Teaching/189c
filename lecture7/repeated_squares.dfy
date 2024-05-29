/*
  ===== Day 24 =====

  (We're in: 189C/lecture7/repeated_square.dfy)

  Announcments:

  - HW3 has been graded!

  - HW4 due Monday, please make use of office hours!
    + My office hours: today 315
    + Parnian office hours: Friday 12pm, Monday 4pm

  - Friday class: I would like to make a recorded lecture instead of Zoom, any objections?

  - See Piazza for other details about upcoming deadlines for HW5 + make-up options

  Plan: Last day of Dafny.

  - Dive in to an activity: Repeated square example

  - Hard stop at 150pm to leave some time to wrap up.

  ===== Poll =====

  Under which of the following circumstances is "false" a valid loop invariant?
  - If the precondition is "true"
  - If the precondition is "false"
  - If the postcondition is "true"
  - If the postcondition is "false"
  - If the loop body is empty
  - If the entire loop block is unreachable code

  https://forms.gle/HEYHHbDueNubK3UB7

  https://tinyurl.com/5d5pz2m4

  ===== Activity today =====

  Work on a harder exercise (as much as we can get through):
  Implement a function that calculates

    pow(x, n) = x^n

  in a more efficient way than just multiplying x by itself n times.
*/

// Here is the easy recursive version.
// We want to write a more efficient version.
function pow(x: int, exp: nat): int
{
  if exp == 0 then 1 else x * pow(x, exp - 1)
}

// Lemmas
/* TODO: add lemmas here as needed */

method RepeatedSquare(x: int, exp: nat) returns (y: int)
  ensures y == pow(x, exp)
  // TODO: Uncomment to implement the function
  requires false
{
  // TODO
}
