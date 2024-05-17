/*
  ===== Day 19 =====

  Introduction to Dafny!

  Last time:
  - We gave a high-level overview of formal verification and why it matters
    (when you might want to use it for a project)
  - We saw that many formal verification tools exist -- for different languages
    and purposes. In this class, we will use the Dafny verification language.
  - Key point: Dafny is both a programming language and a verification tool.

  Plan for today: jump into Dafny syntax and examples!

  Announcements: None!

  Misc:

  - Results of Hypothesis vs Z3 vote:
    Hypothesis: 12
    Z3: 27

  Questions?

  ===== Poll =====

  1. What is formal verification?
  2. Which of the following are the best reasons to use formal verification tools to prove that your code is correct?

  https://forms.gle/12rQLQfZZHUnmDBk6
  https://tinyurl.com/3srvuyt6

  ===== Resources =====

  This file is a modified version of the official Dafny tutorial:
  https://dafny-lang.github.io/dafny/OnlineTutorial/guide

  Thanks to Konstantinos Kallas for an earlier version of the file!
  That version (and a homework) can be found here:
  https://github.com/angelhof/penn-cis673-hw-dafny

  There are many additional resources about Dafny that are useful online.
  I often reference the reference manual:
  https://dafny.org/latest/DafnyRef/DafnyRef

  Rustan Leino, the creator of Dafny, also wrote an excellent textbook,
    *Program Proofs*
    https://mitpress.mit.edu/9780262546232/program-proofs/
  (if you can find a copy of it).

  Finally, there are some good PDF tutorials as well, such as
  (the slightly out of date):
  https://leino.science/papers/krml221.pdf
*/

// Here is the simple Dafny program that we introduced last time:

method Abs(x: int) returns (y: int)
  ensures y >= 0 // <-- specification! (postcondition)
{
  if x >= 0 {
    return x;
  } else {
    return -x;
  }
}

/*
  ===== Syntax =====

  Let's go over the syntax of the code above:

  - "Methods" are functions in standard languages.

    A method is something that you can execute.

    (Note: Dafny also has something called a function, which is a "pure function",
    we will see an example of that later.)

  - We have standard programming constructs (ifs, while loops, etc).

  - The input and output are typed!
    Values have specific types in Dafny.

  - We use `returns` above to indicate that the method returns a value;
    we can also return directly by setting the value y:

  - Dafny uses `:=` for assignment, and `==` for equality of values
    There is no single `=`.
*/

// Equivalent example
method Abs2(x: int) returns (y: int)
  ensures y >= 0
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

/*
  ===== Preconditions and postconditions =====

  We use `requires` to indicate a precondition, and
  `ensures` to indicate a postcondition.

  Last time, we saw that if we modify the code to do something wrong,
  Dafny will catch the error:
  - modifying ensures to a postcondition that is wrong?
  - modifying the return value to return -1 (e.g.)?
  - modifying requires to a precondition that is wrong?

  Summary: Dafny checks whether the spec holds:
  - for *all* inputs satisfying the precondition, after the program
    is run, the output satisfies the postcondition.

  Some design questions:

    Q: Why are return values (like y) named?

    - So that we can refer to them in the postcondition

    Q: Why are values (like x and y) typed?

    - Dafny needs to know the type of a value to be able to
      verify anything about it (and to convert it to a corresponding
      Z3 type).
*/

/*
  ===== Assume and assert =====

  Remember assume and assert?

  - We can use assumptions to tell Dafny we only care about
    executions that satisfy some condition.

  - We can also use assertions to tell Dafny to prove
    that some condition holds at a certain point in the code.

  As we learned with Hypothesis, preconditions and postconditions are
  just special cases of assumptions and assertions!

  What assumptions and assertions might we want to add to Abs?
*/

method Abs3(x: int) returns (y: int)
  ensures y >= 0
{
  if x >= 0 {
    y := x;
    // What assertion could we check here?
    assert y == x;
  } else {
    y := -x;
    // What assertion could we check here?
    assert y == -x;
    // What assumption + assertion could we add here?
    // assume x == -3;
    // assert y == 3;
    // What else?
    // assume x == -2;
    // assert false; // unreachable
    // ^ Assume is dangerous!
  }
}

// Once the code gets compiled, assume and assert statements go away
// in the final binary. That means that assume() statements are like
// cheating, and they are dangerous.

// Q: are integers bounded or unbounded?
// A: They are like in Python, they are unbounded.
//    Dafny does have a bounded int type as well.

// Methods can also have multiple return values, and multiple postconditions.
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y // Comment this out and see what happens!
  ensures less < x
  ensures x < more
{
  more := x + y;
  less := x - y;
  // comments: are not strictly necessary, of course!
}

/*
  Mini-exercise:

  Implement a Max function that returns the maximum of two integers,
  and write pre- and post-conditions for it.

  What kind of pre and postconditions would we like to have here?
*/

method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
  ensures c == a || c == b
  ensures c >= a
  ensures c >= b
{
  // fill in the code here
  // assume false; // remove this line when implemented
  if a <= b {
    c := b;
  } else {
    c := a;
  }
}

// Let's test to see if our method is working!

method TestMax()
{
  var a: int := 5; // The 'int' annotation is optional (it is inferred)
  var b: int := 50;
  var c := Max(a, b);
  assert c == 50;

  // Note that we've "tested" the code without actually running it!
  // We will circle back to that soon as well.
}

/*
  ===== Interfaces and abstraction =====

  The idea of preconditions/postconditions is a useful way to think about
  code in any programming language! But fundamentally, it is a form of
  abstraction:

  - Precondition: what does the method need to do its job?
  - Postcondition: what does the method guarantee to do when it's done?

  Fun fact: the idea of preconditions/postconditions is also known as
  "Design by Contract". The idea is that you can think of a method as
  a contract between the caller who wants something from the method, and the
  method, which provides that thing.

  There's a bit of a problem with Abs, though.
  To see what it is,
  in Dafny, let's see what happens when we try to use a test with Abs!
*/

method TestAbs()
{
  // What should we assert about Abs?

  var x: int := Abs(5);
  assert x >= 0;
  // Uncomment these lines, what happens?
  // var x := Abs(5);
  // assert x == 5;
}

/*
  Why didn't this work?

  This is because Dafny abstracts methods away by their pre and postconditions
  to simplify verification. This means that it doesn't look inside Abs' definition
  to verify the assertion, but rather uses the knowledge that it has of Abs' model.

  What's left of the method is only the pre and postconditions!

  This is a common scenario in formal verification: it often happens
  that the verifier doesn't have enough information to prove a property.
  And, we need to strengthen the model by making the postcondition stronger.

  What postconditions should we add to Abs to fix it?
*/

method AbsFixed(x: int) returns (y: int)
  // TODO: Fixed postcondition:
  ensures y >= 0
  ensures y == x || y == -x
  // The interface is complete! The contract fully specifies
  // what the output should be on every input.
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

method TestAbsFixed()
{
  var x := AbsFixed(5);
  assert x == 5;
}

/*
  However, our spec now describes exactly the body of the method, which is a bit redundant.

  That's what functions are for! We will see this next time.

  Recap:
  - We saw how to define basic methods (procedures) in Dafny
  - We saw the basic syntax for preconditions, postconditions,
    assume/assert, and how to write tests.
  - We will continue with more Dafny features next time!

  ***** Where we left off for Day 19 *****

  ===== Day 20 =====

  Announcements:

  - Dafny installation instructions:
    installation instructions on Windows/Linux/Codespaces
    are posted in the README.md
    (These will also be made available with HW4.)

  - HW4 release will be posted on Piazza when ready;
    you will have at least 2 weeks to complete once released.

  Plan:

  - Continue with more Dafny concepts:
    + functions and expressions
    + running the code
    + strongest postconditions and weakest preconditions
    + recursion and loops

  Questions?

  ===== Poll =====

  Consider the following Double method:
*/

method Double(x: int) returns (y: int)
  // requires ... ensures ...
{
  y := x + x;
}

// Which of the following pre/postconditions can we add
// to get the following test to pass?

method TestDouble()
{
  var x := Double(5);
  // assert x == 10; // Uncomment this line
}

/*
  1. nothing (the test will pass as is)
  2. requires x == 5
  3. ensures y == 10
  4. ensures y == x + x
  5. requires x == 0 ensures y == x + x
  6. requires x == 5 ensures y == 10
  7. requires false
  8. ensures false
  9. requires (x == 5 ==> y == 10)
  10. ensures (x == 5 ==> y == 10)

  https://forms.gle/dV3uswiZnvz7BRdt7
  https://tinyurl.com/wk6fvfvm

  (After poll: try it out)
*/

/*
  ===== Functions =====

  Last time, we saw that we can't prove that Abs(5) == 10
  unless we give it a strong postcondition.
  This same problem occurs with options (1) and (2) above:
  (Why?)

  The reason? *Abstraction:* A Dafny method is considered abstracted
  by only its pre/postcondition behavior.

  Dafny has a solution for this, and allows us to define
  mathematical functions
  that are not opaque when the Dafny verifier runs:
*/

function abs(x: int): int
{
  if x >= 0 then x else -x
}

method TestAbsEasier()
{
  // TODO
}

/*
  Functions expose another important concept in Dafny:
  only functions can be used in expressions!

  What happens when we try to call AbsFixed(5) in an expression?
  What happens when we try to call abs(5) in an expression?

  (We ran into this problem last time!)
*/

method TestAbsExpression()
{
  var x := AbsFixed(5); // This is fine
  // assert AbsFixed(5) == 5; // Error
  var y := abs(5); // This is fine
  assert abs(5) == 5; // This is fine
}

/*
  What's the reason for this?

  Functions represent mathematical functions: every time the function is called
  on the same input, it will return the same output.

  (If you've heard of the idea of "functional programming" or "pure functions",
  that's what functions in Dafny are like. There are whole languages dedicated to
  this, like Haskell.)

  Methods represent procedures: they can have side effects, and can return different
  results on the same input (in theory).

  That means that it's not a valid thing to use in an assertion.
  Why?

  Recap:
  We've already learned the basics of verifying simple Dafny code!
  Methods (and tests), functions, preconditions, postconditions,
  tests, and assert/assume.

  Before we continue with more complex examples,
  I have a couple of digressions to make.
*/

/*
  ===== Digression 1: Running the code? =====

  You may have noticed something odd: we haven't run any code yet!
  In fact, even in our Tests, all we did was ask Dafny to verify that the test
  would pass.

  But that doesn't mean Dafny can't run the code!

  Dafny is a *verification-aware* programming language.
  That means, it can verify your code, but it can also compile/run it!

  To run the code, we just need a Main() function:
*/

method Main()
{
  var x: int := -5;
  var y: int := Abs(x);
  print "x = ", x, ", y = ", y, "\n";
}

/*
  To run from the command line, we can use the `dafny` command.
  Here are some of the options:

  1. `dafny verify lecture.dfy` -- to run the verifier only.
      This is equivalent to what we've been doing so far (checking the green
      bar on the left in VSCode).

  2. `dafny build lecture.dfy` -- to compile to a library, dafny.dll
     (This is also run by default with `dafny lecture.py`)
     We won't use this option much in this class.

  3. `dafny run lecture.dfy` -- to run the code!

  If we have warnings in the code, Dafny will refuse to compile the code;
  however, you can turn this off by adding the flag
    --allow-warnings
  You will get warnings if you use `assume` for example! (Why?)
  In general, it's best to remove all warnings before running the code.
*/

// Here's another example from the Dafny reference:
// datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)
// method Main()
// {
//   var x : Tree := Node(Node(Empty, 1, Empty), 2, Empty);
//   print "x=", x, "\n";
// }

/*
  There's also a fourth option to run Dafny!
  Perhaps you remember from last time, that one of the advantages of Dafny
  is that it can produce output in other languages, so it can integrate
  with your existing workflow.
  Try this:

  4. `dafny build --target:py lecture.dfy`

  This produces output in: lecture-py/module_.py.
  (You can ignore the other files.)
*/

/*
  ===== Digression 2: strongest postconditions and weakest preconditions =====

  We saw above that in order to prove properties about
  methods like Abs and Double,
  we needed to strengthen the postcondition to be stronger
  (or use a function instead of a method.)
  Is the new postcondition really as strong as it can be?

  On HW1, part 1B, you were asked to write specifications that are the
  *strongest possible* description of what the function does.
  What does that mean?

  Let's define:

  - The *strongest postcondition* of a statement is the strongest condition
    that is guaranteed to hold after executing the statement, given that the
    precondition holds.

  - The *weakest precondition* of a statement is the weakest condition
    that guarantees that the postcondition will hold after executing the statement.

  Here are some examples based on the Abs function;
  we will see more about this later!
*/

method StrongestPostconditionEx(x: int) returns (y: int)
  requires x >= 5
  // TODO: what ensures statement should go here?
{
  y := Abs(x + x);
}

method WeakestPreconditionEx(x: int) returns (y: int)
  // TODO: what requires statement should go here?
  requires false // Replace this line
  ensures y >= 10
{
  y := Abs(x + x);
}

// What about this? (A harder one)
method StrongestPostconditionEx2(x: int) returns (y: int)
  requires x >= 5
  // TODO: what ensures statement should go here?
  // Let's figure it out!
{
  if x <= 10 {
    y := Abs(x +  x + x);
  } else {
    y := Abs(x + x);
  }
}

/*
  Strongest postconditions and weakest preconditions are a key part of how
  Dafny works internally -- it is calculating them implicitly all the time!

  The way it does it is basically the process we did above.

  The process of fixing Abs and Double -- in order to make the
  postcondition as strong as possible, so the test passes --
  was basically about finding the strongest postcondition for the
  method.
*/

/*
  ===== Recursion and loops =====

  So far, the examples we've seen are quite simple; we could have done any
  of this in Z3 pretty easily!

  Loops and recursion is where program verifiers become both
  much more powerful (expressive) -- and more effort-intensive.

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
  ===== Another digression: the limits of verification? =====

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
  ===== Arrays =====

  Dafny supports imperative arrays. The only difference with C is that the array has its length in the data structure.
*/

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index < a.Length ==> (index < a.Length && a[index] == key)
  ensures index == a.Length ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  // Can we write code that satisfies the postcondition?
  index := 0;
  while (index < a.Length) && (a[index] != key)
    decreases a.Length - index
    invariant 0 <= index <= a.Length
    invariant forall j : nat :: j < index ==> a[j] != key
  {
    // if a[index] == key
    // {
    //    return ;
    // }
    index := index + 1;
  }
  // index := -1;
  // return -1;
}

// If we have time we can also look at this FindMax
// method FindMax(a: array<int>) returns (max_i: int)
//    requires a.Length > 0
//    ensures 0 <= max_i < a.Length
//    ensures forall k :: 0 <= k < a.Length ==> a[max_i] >= a[k]
// {

// }

// Our postconditions and invariants are starting to grow big
//   (especially when dealing with arrays)
//   and so we would like to abstract away parts of them.
//
// For that, we can use predicates, i.e., boolean functions that can only be used in specifications.

// Let's write a predicate that holds if its input array is sorted.

predicate sorted(a: array<int>)
  reads a // Necessary to give ownership to a predicate (or function) to read/write an array
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// And now to gather everything that we have seen in the lecture already,
//   let's write the spec for a binary search, and then implement and verify it.
//
// We will go through the whole process, debugging whatever might go wrong etc.
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  // modifies a
  // During the lecture: Write pre and postconditions
  ensures 0 <= index ==> (index < a.Length && a[index] == value)
  ensures 0 > index ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  // inclusive low, exclusive high
  var low := 0;
  var high := a.Length;

  while low < high
    decreases high - low
    invariant 0 <= low <= high <= a.Length
    invariant forall j :: 0 <= j < low ==> a[j] < value
    invariant forall j :: high <= j < a.Length ==> a[j] > value
    invariant sorted(a)
  {

    var i := (high + low) / 2;
    if a[i] > value
    {
      high := i;
    }
    else if a[i] < value
    {
      low := i + 1;
      var temp_ai := a[i];
      assert forall j :: high <= j < a.Length ==> a[j] > value;
      assert low > 0 ==> a[low - 1] < value;
      assert forall j :: 0 <= j < low ==> a[j] < value;
    }
    else
    {
      return i;
    }
  }
  return -1;
}

//
// Allocating arrays
//

// Until now for simplicity we haven't shown any array allocation, but Dafny allows that too with the `new` keyword.

method Copy(a: array<int>) returns (b: array<int>)
{
  b := new int[a.Length];
}

//
// Sequences
//

// I will now give a brief overview of sequences to show how they facilitate verification.
//   For a more complete reference see: (https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf)

// Let's say we wanted to write a predicate that holds if a slice of the array was sorted

predicate sorted_slice(a: array<int>, start: int, end: int)
  reads a
  requires 0 <= start < end < a.Length
{
  forall i,j :: start <= i < j < end ==> a[i] <= a[j]
}

// yuck

// Sequences can help by allowing for easy slicing and slightly more succint syntax.
//   Also they are immutable meaning that Dafny doesn't need to care about whether they are modified or not.


predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// And let's use it

method TestSeq(a: array<int>)
  // requires sorted_seq(a[0..10])
{

}

//
// Auxiliary State
//

// The final thing that one needs to know for the homework is that often
//   the implementation code is not adequate for dafny to verify postconditions
//   (especially in the presence of loops).
//
// In addition to the original code and state, there is often need for
//   extra auxiliary state (variables, arrays) that can help establish a fact that is needed for a postcondition.
//
// An example of such extra state that might be helpful is a data structure that "logs" some important actions
//   that were done in the loop.

// And finishing with a quote from the official dafny tutorial
//
// ```
//    Even if you do not use Dafny regularly, the idea of writing down exactly
//    what it is that the code does in a precise way, and using this to prove code correct
//    is a useful skill. Invariants, pre- and postconditions, and annotations are useful
//    in debugging code, and also as documentation for future developers. When modifying
//    or adding to a codebase, they confirm that the guarantees of existing code are not broken.
//    They also ensure that APIs are used correctly, by formalizing behavior and requirements
//    and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions,
//    and writing assertions to check assumptions are all general computer science skills
//    that will benefit you no matter what language you work in.
// ```
