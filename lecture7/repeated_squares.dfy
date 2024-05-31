/*
  ===== Day 24 =====

  (We're in: 189C/lecture7/repeated_square.dfy)

  Announcments:

  - HW3 has been graded!

  - HW4 due Monday, please make use of office hours!
    + My office hours: today 315
    + Parnian office hours: Friday 12pm, Monday 4pm

  - Friday class: I would like to make a recorded lecture instead of Zoom, any objections?

  - See Piazza for other details about upcoming deadlines for (optional) HW5 + make-up options

  Plan: Last day of Dafny.

  - Start with the poll

  - Dive in to an activity: Repeated square example

  - Hard stop at 150pm to leave some time to wrap up.

  Questions about HW4?

  ===== Poll =====

  Under which of the following circumstances is "false" a valid loop invariant?
  (Valid: remember the three conditions (i)-(iii) of a loop invariant!)
  (Select all that apply)
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

  (E.g. pow(3, 2) == 9, exponent function from basic arithmetic.)

  in a more efficient way than just multiplying x by itself n times.

  Similar approach to examples we've seen before:
  - Define a function version that is "obviously" correct
  - Write a more complicated algorithm, and prove that it's equivalent
    to the function version.
*/

// Here is the easy recursive version.
// We want to write a more efficient version.
function pow(x: int, exp: nat): int
{
  if exp == 0 then 1 else x * pow(x, exp - 1)
}

/*
  Running time?
  Linear in the exponent: O(exp)

  Can we do better?

  - If the exponent is even?

    exp == 100

    We could calculate like this:
    x^100 == (x^50) * (x^50)

    50 recursive calls instead of 100
    O(exp / 2)
    unfortunately that's still O(exp)

    So, let's try to do this recursively!

    What should we do in the odd case?

    Subtract one from the exponent, then treat it's like it's even.

    x^101 == x * (x^50) * (x^50)

  This is the basic idea behind the
  square and multiply algorithm (a.k.a. "repeated squaring")

  Instead of doing it recursively (as suggested above), let's
  implement it iteratively, as iterative code tends to be the
  most efficient in practice.
*/

// Lemmas
lemma PowSquare(base: int, exp: nat)
  ensures pow(base, 2 * exp) == pow(base * base, exp)
{
  // Lemma can be proven directly in this case, does not need
  // any help. So the function body is empty.
}

method RepeatedSquare(x: int, exp: nat) returns (y: int)
  ensures y == pow(x, exp)
{
  // Variables to maintain?
  // Repeated squaring: we start with x,
  // then x^2, then x^4, then x^8, and so on.
  // As we go along squaring, we should tally the total product
  // so far.
  // Ex: x^13
  // 13 == 8 + 4 + 1, so x^13 = x^8 * x^4 * x^1
  // So in our while loop, we should multiply by the x^1, x^4, and x^8 cases.
  var running_square := x;
  var running_product := 1;
  var exp_remaining := exp;

  while exp_remaining > 0
    // Loop invariant
    invariant running_product * pow(running_square, exp_remaining) == pow(x, exp)
    // Equivalent to the following,
    // using a ghost variable i to enumerate the loop iterations:
    // running_product * pow(x, exp_remaining * pow(2, i)) == pow(x, exp)
  {
    // Work backwards debugging method!
    // Once we work backward to push the invariant all the way to the
    // top of the loop, we can see what's missing to prove the invariant
    // from the top-of-the-loop invariant that we have.
    // 2 cases:
    // - we may need to strengthen the invariant
    // - we may need to add a lemma if the missing step is true,
    //   and Dafny just can't figure it out.

    // Full proof finished after lecture

    assert running_product * pow(running_square, exp_remaining) == pow(x, exp);
    assert exp_remaining > 0;

    // Ghost vars to help track things in the assertions
    ghost var old_prod := running_product;
    ghost var quot := exp_remaining / 2;
    ghost var rem := exp_remaining % 2;
    assert exp_remaining == quot * 2 + rem;

    if exp_remaining % 2 == 1 {
      assert rem == 1;

      running_product := running_square * running_product;
    }

    assert old_prod * pow(running_square, exp_remaining) == pow(x, exp);
    assert running_product == old_prod * pow(running_square, rem);
    assert (
        running_product * pow(running_square, exp_remaining)
        == pow(x, exp) * pow(running_square, rem)
      );
    assert (
        running_product * pow(running_square, 2 * quot + rem)
        == pow(x, exp) * pow(running_square, rem)
      );
    assert (
        running_product * pow(running_square, 2 * quot)
        == pow(x, exp)
      );

    // Here we identify the lemma we need to prove
    // To finish the proof, we add a lemma above and
    // call it to bring it into scope.
    PowSquare(running_square, quot);
    // Lemma proves the following assertion
    assert (
        pow(running_square, 2 * quot)
        ==
        pow(running_square * running_square, quot)
      );

    assert running_product * pow(running_square * running_square, quot) == pow(x, exp);

    assert running_product * pow(running_square * running_square, exp_remaining / 2) == pow(x, exp);

    exp_remaining := exp_remaining / 2;
    running_square := running_square * running_square;

    assert running_product * pow(running_square, exp_remaining) == pow(x, exp);
  }
  y := running_product;
}
