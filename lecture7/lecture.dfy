/*
  ===== Loops and recursion =====

  So far, the examples we've seen are quite simple; we could have done
  any of this in Z3 pretty easily!

  Loops and recursion is where program verifiers become both
  much more powerful (expressive) -- as well as more effort-intensive,
  since verifying a program with loops is a hard problem in general,
  and can't always be done automatically.

  Let's start with recursion:
  Functions support recursion and can appear in expressions!

  Let's define a function that computes a given fibonaci number:
*/
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n-1) + fib(n-2)
}

/*
  This function would be really slow due to recomputations if implemented as is,
  so let's implement a fast method, and prove that it is equivalent.

  We first need a loop, and then we will see one of the main very important notions of verification: loop invariants.

  ===== Loop invariants =====

  What is a loop invariant?

  A loop invariant is an assertion that must hold
  after *every* loop iteration. Like this:

    assert <invariant>;
    while P {
      <loop body>
      assert <invariant>;
    }

  Loop invariants are the key to verifying real-world code,
  and they are often the hardest part to come up with.
  We need to "guess" an invariant that both
  (i) is satisfied before the loop runs
  (ii) is preserved by the loop
  (iii) is strong enough to prove what we want after the loop
*/

method ComputeFib(n: nat) returns (b: nat)
  // TODO: uncomment to implement the function
  // ensures b == fib(n)
{
  if (n <= 0)
  {
    return n;
  }
  else
  {
    var prev := 0;
    var curr := 1;

    var i := 1;
    while i < n
      // invariant ...
    {
      curr, prev := curr + prev, curr;
      i := i + 1;
    }
    return curr;
  }
}

/*
  ===== Termination =====

  There's another thing that's implicitly going on with recursion and while loops:
  program termination.

  Exercise: add a decreases clause to both functions.

  What does the decreases clause ensure?
*/

/*
  ===== Digression 3: the limits of verification? =====

  Let's take a step back and consider what we've done so far.
  - We managed to write a function to calculate Fibonacci numbers and
    *prove* that it's always correct, on all inputs. Without ever running
    the code.

  - It was a bit difficult though: we had to come up with a special "loop invariant"
    and (in theory) a "decreases" clause to make it work,
    and the code wouldn't verify otherwise.
    So is this always possible?

  There's sort of an argument for NO and an argument for YES.

  NO: Some of you may have heard that proving general properties
  about programs is supposed to be impossible!
  (It's OK if you haven't heard this.) For example,
  we know that the halting problem is impossible to decide:

    HALT(x) = "Does program x halt?"

  There's no program which decides the above!
  Yet, Dafny is able to determine not just that all the programs halt,
  but that they are correct (satisfy the spec) on all inputs.
  So in Dafny, we could decide the halting problem this way:

    HALT(x): return true;

  Let's take a minute to appreciate what that means: using just some math
  equations and formulas, and a fancy verification tool (which uses Z3),
  we know (without running it) that the program will give the correct
  answer on **all possible inputs.** Not just some particular
  inputs that we tried. It's a way to completely fool-proof all future uses
  of the code.

  YES: The surprising thing (at least if you've taken theory of computation)
  is that in practice, yes, it is almost always possible to prove that
  programs correct.

  People have even built entire software projects: like cryptographic libraries,
  operating system kernels, and (famously) an optimizing C compiler (CompCert)
  entirely in formally verified programming languages.
    https://sel4.systems/About/
    https://compcert.org/

  If program termination and correctness is undecidable in general, then how
  are these projects possible?

  Any ideas? :)

  Answer:
*/

/*
  ===== Sequences and arrays =====

  Loops and invariants become especially useful when working
  with more complex data types, like sequences.
  Let's give an overview of these.

  The homework will be mostly about more basic data types, but there
  are a few questions about sequences. We won't need arrays.

  Dafny supports sequences seq<int> and imperative arrays array<int>.
  These are basically list types (like Python lists or C++ vectors).

  Sequences are immutable, and arrays are mutable.
  Due to the subtleties of mutability, arrays can be more advanced
  to work with.
*/

method Find(a: seq<int>, key: int) returns (index: int)
  ensures 0 <= index < |a| ==> (index < |a| && a[index] == key)
  ensures index == |a| ==> forall k :: 0 <= k < |a| ==> a[k] != key
  // TODO: remove to implement
  requires false
{
  // Can we write code that satisfies the postcondition?
  index := 0;
  while (index < |a|) && (a[index] != key)
    // TODO: Implement the loop invariant
  {
    index := index + 1;
  }
}

// If we have time we can also look at this:
// Find the maximum element in a sequence
// method FindMax(a: seq<int>) returns (max_i: int)
//    requires a.Length > 0
//    ensures 0 <= max_i < a.Length
//    ensures forall k :: 0 <= k < a.Length ==> a[max_i] >= a[k]
// {
// }

/*
  Array example: allocating a new array

  Until now for simplicity we haven't shown any data type
  allocation, but Dafny allows allocating with the `new` keyword.
*/

method Copy(a: array<int>) returns (b: array<int>)
{
  b := new int[a.Length];
  // TODO: copy the array over
  // This will be a HW problem
}

// It can be useful to define predicates that can be used in
// pre/postconditions to make the code more readable.

// A predicate is just a function that returns a boolean.
// Dafny provides as `predicate` keyword but you can also
// just use `function`.

// Predicate that holds if a sequence is sorted
predicate sorted_eq(a: seq<int>, start: int, end: int)
  requires 0 <= start < end < |a|
{
  forall i,j :: start <= i < j < end ==> a[i] <= a[j]
}

// Array version: note the `reads` clause
// We won't see `reads` a lot in this class, but it will show up on
// part 2 of the homework.
predicate sorted_array(a: array<int>, start: int, end: int)
  reads a
  requires 0 <= start < end < a.Length
{
  forall i,j :: start <= i < j < end ==> a[i] <= a[j]
}

/*
  Selection of other/advanced concepts

  ===== Lemmas =====

  A lemma is written as a method that provides
  an additional postcondition. A lemma may or may not have a body.
  You can write one like this:

  method Lemma(a: seq<int>)
    ensures <some conditions>
  {
  }

  To call the lemma, you just call the method.
  It brings the postcondition assert in scope so that Dafny
  can use it to verify the code in the location you're working on.

  // Call the lemma
  Lemma();
  // Prove some additional assertions that were failing using the lemma
  assert <some hard condition>;

  ===== Ghost variables and auxiliary state =====

  Sometimes the implementation code is not adequate for dafny to verify
  postconditions (especially in the presence of loops).
  Ghost variables are additional state that you can track in the program
  that is not part of the actual implementation.

  An example of such extra state that might be helpful is a data structure that "logs" some important actions
  that were done in the loop.

  More generally, Dafny's concept of "ghost" is related to the idea of
  abstraction.
  Ghost data are any data that are removed away at runtime,
  and only present at compile time.

  ===== Practice: a harder programming exercise =====

  Let's do a harder exercise: defining an optimized
  version of the power function.

  **See repeated_squares for this exercise.**
*/

/*
  Finishing with a quote from the Dafny tutorial:
  https://dafny.org/latest/OnlineTutorial/guide

  Even if you do not use Dafny regularly, the idea of writing down exactly what it is that the code does is a precise way, and using this to prove code correct is a useful skill. Invariants, pre- and post conditions, and annotations are useful in debugging code, and also as documentation for future developers. When modifying or adding to a codebase, they confirm that the guarantees of existing code are not broken. They also ensure that APIs are used correctly, by formalizing behavior and requirements and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions, and writing assertions to check assumptions are all general computer science skills that will benefit you no matter what language you work in.
*/
