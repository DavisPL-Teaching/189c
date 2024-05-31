/*
  ===== Loops and recursion =====

  So far, the examples we've seen are quite simple; we could have done
  any of this in Z3 pretty easily!

  Loops and recursion is where program verifiers (like Dafny) become both
  much more powerful (expressive) -- as well as more effort-intensive,
  since verifying a program with loops is a hard problem in general,
  and can't always be done automatically.

  Remember: we saw that we could use weakest preconditions and
  strongest postconditions to basically automatically verify (or
  generate correct pre/postcondition specs) for any function.
  However, this only worked for programs without loops or recursion.

  Missing piece of the puzzle: what to do about loops and recursion?

  Let's start with recursion:
  Functions support recursion and can appear in expressions!

  Let's define a function that computes a given fibonaci number:

  nat: a shorthand for a "natural number", i.e. nonnegative integer
  BTW: nat is just shorthand for
  int with precondition n >= 0 and postcondition output >= 0
*/
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n-1) + fib(n-2)
}

// Reminder: since function syntax uses expressions, there are
// no "return" keywords". We just directly state the return value.
// "0" instead of "return 0".

/*
  This function would be really slow due to recomputations if implemented as is,
  so let's implement a fast method, and prove that it is equivalent.

  First, let's see why this is a bad/slow implementation:
  fib(5) == fib(4) + fib(3)
    == (fib(3) + fib(2)) + (fib(2) + fib(1))
    == (fib(2) + fib(1)) + (fib(1) + fib(0)) +
      (fib(1) + fib(0)) + 1
    == fib(1) + fib(0) + fib(1) + fib(1) + fib(0) + fib(1) + fib(0) + 1
    == 1 + 0 + 1 + 1 + 0 + 1 + 0 + 1 == 5.

  Very inefficient! The same value, like fib(3) or fib(2), is getting
  expanded out multiple times.
  It becomes much worse if we calculate something like fib(10) or
  fib(20).
  (Exercise: try this out in Python.)

  Situation:
  - we have a slow/correct implementaiton
  - we define a fast optimized implementation
  - we want to prove that the fast implementation is equivalent to
    the slow/correct one.

  We first need a loop, and then we will see one of the main very important notions of verification: loop invariants.

  ===== Loop invariants =====

  What is a loop invariant?

  A loop invariant is an assertion that must hold
  after *every* loop iteration. Like this:

    assert <invariant>; // loop invariant
    while P {
      <loop body>
      assert <invariant>; // loop invariant
    }

  Loop invariants are the key to verifying real-world code,
  (real-world code has a lot of loops in it)
  and they are often the hardest part to come up with.
  We need to "guess" an invariant that both
  (i) is satisfied before the loop runs
  (ii) is preserved by the loop
  (iii) is strong enough to prove what we want after the loop

  Dafny will verify that all of (i), (ii), (iii) is true.
  It will not allow you to pick an invariant that's wrong.
*/

method ComputeFib(n: nat) returns (b: nat)
  // Postcondition: the output is the same as fib(n)
  ensures b == fib(n)
{
  if (n == 0)
  {
    // No while loop -- simple enough for Dafny to verify
    return n;
  }
  else
  {
    var prev := 0; // stores the previous fib number: fib(0)
    var curr := 1; // stores the current fib number: fib(1)

    var i := 1;

    // O(n) loop iterations
    while i < n
      // Loop invariant syntax
      invariant i >= 1
      invariant i <= n
      invariant curr == fib(i)
      invariant prev == fib(i-1)
    {
      // Let's think about what the code is doing.
      // On entering the loop:
      // curr, prev == 1, 0 (i == 1)
      // After first iteration of the loop:
      // curr, prev := 1 + 0, 1 ---> 1, 1, (i == 2)
      // After second iteration of the loop:
      // curr, prev := 1 + 1, 1 ---> 2, 1 (i == 3)
      // After third iteration of the loop:
      // curr, prev := 2 + 1, 2 ---> 3, 2 (i == 4)
      // After fourth iteration of the loop:
      // curr, prev := 3 + 2, 3 --> 5, 3 (i == 5)

      curr, prev := curr + prev, curr;
      i := i + 1;
    }
    // What information does Dafny have here?
    // After a while loop, Dafny isn't sure what's true or not
    return curr;
  }
}

/*
  ##### where we left off for Day 22 #####

  ===== Day 23 =====

  Announcements:

  - Please start HW4 if you haven't yet!
    + Office hours today 330, I can help with installation issues
    + We may not be able to keep helping with installation
      issues in next week's office hours.

  - The people have spoken: HW5 is cancelled!
    + 27 votes for cancel
    + 6 votes for keep
    + I will release the homework on Piazza later today.
    + I will be able to offer a very small amount of points for extra credit (5)
      as a small incentive.
    + Due June 6

  Plan:
  Finish things we need to cover for the homework:

  - Fix the loop invariant and recap (from end of last time)

  - Poll

  - Remaining stuff we need to cover for the HW
    + Sequences
    + Lemmas

  - I have lots of additional topics in advanced.dfy and repeated_squares.dfy
    we could do next time.

  Questions?

  ===== Poll =====

  https://forms.gle/Q44qm1Ve27xrpdRMA
  https://tinyurl.com/mmu2scjs

  Here's a very inefficient version of a function
  that copies a nonnegative integer.

  Write a loop invariant that will allow us to prove CopyInt.

  Remember, a loop invariant must be:
  (i) true before entering the loop,
  (ii) preserved by the loop body
  (iii) imply the postcondition after the loop ends
*/

method CopyInt(a: nat) returns (b: nat)
  // Uncomment to try the example
  // requires a >= 0
  ensures b == a
{
  var i: nat := a;
  b := 0;
  while i > 0
    // Technically these were not needed
    invariant i <= a
    invariant b >= 0
    invariant i >= 0
    // The right invariant!
    invariant a == b + i
    // This also works
    // invariant a - i == b
  {
    i := i - 1;
    b := b + 1;
  }
  // What do I know here?
  // (For the invariant above: i <= a, b >= 0)
  // a - i == b? (no)
  // i == 0, b == a? (no)
  // i <= 0 <-- since the loop terminated
  // i <= a && b >= 0 <-- invariant
  // We don't know that a == b.
}

// Another one -- SKIP
method AddOne(a: nat) returns (b: nat)
  // Uncomment to try the example
  // ensures b == a + 1
{
  b := 0;
  while b < a + 1
    // invariant ...
  {
    b := b + 1;
  }
}

/*
  ===== Sequences =====

  Loops and invariants become especially useful when working
  with more complex data types, like sequences.
  Let's give an overview of these.

  A sequence is basically a list. To create a new sequence:

    b := [];
    b := [1, 2, 3];

  The homework will be mostly about more basic data types, but there
  are a few questions about sequences.

  Sequences are immutable.
  Dafny supports sequences seq<int> and imperative arrays array<int>,
  which are mutable. Wwe won't use arrays on the homework.
*/

method Find(a: seq<int>, key: int) returns (index: int)
  ensures 0 <= index < |a| ==> a[index] == key
  ensures index == |a| ==> forall k :: 0 <= k < |a| ==> a[k] != key
{
  // Can we write code that satisfies the postcondition?
  index := 0;
  while (index < |a|) && (a[index] != key)
    invariant index <= |a|
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    index := index + 1;
  }
  // We know that index == |a| OR a[index] == key
  // We know that forall k :: 0 <= k < |a| ==> a[k] != key
}

// SKIP: a similar example
// Find the maximum element in a sequence
// method FindMax(a: seq<int>) returns (max_i: int)
//    requires a.Length > 0
//    ensures 0 <= max_i < a.Length
//    ensures forall k :: 0 <= k < a.Length ==> a[max_i] >= a[k]
// {
// }

/*
  Selection of other/advanced concepts

  ===== Lemmas =====

  A lemma is written as a method that provides
  an additional postcondition. A lemma may or may not have a body.
  You can write one like this:

  lemma MyLemma(a: seq<int>)
    ensures <some conditions>
  {
  }

  (A plain method should also work, though using the lemma keyword is more idiomatic
  for reasons we will not go into here.)

  Imagine:
    You're trying to prove a function, and Dafny gets stuck somewhere
    in the function, it can't figure out that
      a[i + j] + a[j - 4] == a[j - 4] + a[i + j]

  Example: write a lemma that addition is commutative:
    a + b == b + a
*/

lemma AdditionCommutative(a: int, b: int)
  ensures a + b == b + a
{
  // Done
}

// To use the lemma:
// At the place where Dafny is stuck:
/*
  AdditionCommutative(a[i + j], a[j - 4]);
*/

/*
  Example: write a lemma that pow satisfies each of:
    pow(x, exp + 1) == x * pow(x, exp)
    pow(x, exp1 + exp2) == pow(x, exp1) * pow(x, exp2)
*/

function pow(x: int, exp: nat): int
{
  if exp == 0 then 1 else x * pow(x, exp - 1)
}

/*
  To call the lemma, you just call the method.
  It brings the postcondition assert in scope so that Dafny
  can use it to verify the code in the location you're working on.

  // Call the lemma
  Lemma();
  // Prove some additional assertions that were failing using the lemma
  assert <some hard condition>;

  ===== Practice: a harder programming exercise =====

  Let's do a harder exercise: defining an optimized
  version of the power function.

  **See repeated_squares for this exercise.**
*/

/*
  What are the main advantages and limitations of Dafny?

  - Invariants are very difficult to figure out (even for a human!) and very
    effort intensive

  - It inherits some of the same limitations of Z3
    + If Z3 returns unknown or times out, Dafny also doesn't know what to do
    + This is exactly what makes verification sometimes so difficult: we need
      to add more information to help Dafny get through the assertion and give
      it enough information to pass to Z3 so that Z3 knows the assertion is true.
    + This is actually both a benefit and a drawback, as unlike
      with Z3 where it can be unclear what additional information
      to add to get the proof to work (we saw this somewhat in HW3),
      with Dafny we at least know that we can add some additional
      information to eventually get the proof to go through.

  Summary:
    - A lot more expressive and general; but
    - A lot more effort intensive to get the proofs to go through.
*/

/*
  Finishing with a quote from the Dafny tutorial:
  https://dafny.org/latest/OnlineTutorial/guide

  Even if you do not use Dafny regularly, the idea of writing down exactly what it is that the code does is a precise way, and using this to prove code correct is a useful skill. Invariants, pre- and post conditions, and annotations are useful in debugging code, and also as documentation for future developers. When modifying or adding to a codebase, they confirm that the guarantees of existing code are not broken. They also ensure that APIs are used correctly, by formalizing behavior and requirements and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions, and writing assertions to check assumptions are all general computer science skills that will benefit you no matter what language you work in.
*/
