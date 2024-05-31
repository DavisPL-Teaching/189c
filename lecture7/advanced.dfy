/*
  Advanced topics that we did not cover in lecture

  - Predicates
  - Arrays (and mutation)
  - Ghost variables and auxiliary state
  - Program termination
  - Philosophical discussion: the limits of verification
*/

/*
  ===== Predicates =====
*/

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

/*
  ===== Arrays =====

  Arrays are kind of like sequences but they are mutable instead
  of immutable, so more useful in writing real code.
  Arrays are not covered on the homework. Using them is more
  complicated, as we have to worry about what parts of memory
  are read and written to (`reads` and `modifies` clauses)
  that can be somewhat subtle.

  Very basic array example: allocating a new array

  (Until now for simplicity we haven't shown any data type
  allocation, but Dafny allows allocating with the `new` keyword.)
*/

method Copy(a: array<int>) returns (b: array<int>)
{
  b := new int[a.Length];
  // TODO: copy the array over
  // This is a HW problem, but on the HW we do it with sequences instead
}

// Array version of the `sorted` predicate: note the `reads` clause
// We won't see `reads` a lot in this class, but it will show up on
// part 2 of the homework.
predicate sorted_array(a: array<int>, start: int, end: int)
  reads a
  requires 0 <= start < end < a.Length
{
  forall i,j :: start <= i < j < end ==> a[i] <= a[j]
}

/*
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
*/

/*
  ===== Termination =====

  There's another thing that's implicitly going on with recursion and while loops:
  program termination.

  Exercise: add a decreases clause to both the fib and ComputeFib
  functions.

  What does the decreases clause ensure?
*/

/*
  A more philosophical discussion :)

  ===== The limits of verification? =====

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
