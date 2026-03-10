/*
    Lecture 4, Part 4: Loops and loop invariants.

    === Intro ===

    The missing piece of the puzzle!

    So far, the examples we've seen are quite simple; we could have done
    any of this in Z3 pretty easily!

    Loops and recursion is where interactive program verifiers (like Dafny) become both
    much more powerful (expressive) -- but at the same time, more effort-intensive,
    since verifying a program with loops is a hard problem in general,
    and can't always be done automatically.

    Remember: we saw that we could use weakest preconditions and
    strongest postconditions to basically automatically verify (or
    generate correct pre/postcondition specs) for any function.

    However, this only works for programs without loops or recursion!

    ===== Loops and recursion =====

    Let's start with recursion:
    Functions support recursion and can appear in expressions!

    Let's define a function that computes a given Fibonacci number:

    nat: a shorthand for a "natural number", i.e. nonnegative integer
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

    First informally:
    A loop invariant is an assertion that must hold
    *before* the loop executes and
    *after* every loop iteration. Like this:

        assert <invariant>; // loop invariant
        while P {
            <loop body>
            assert <invariant>; // loop invariant
        }

    Loop invariants are the key to verifying real-world code,
    (real-world code has a lot of loops in it)
    and they are often the hardest part to come up with.

    The above is not quite a definition that works for Dafny to check
    automatically though!
    It turns out we actually need something stronger.

    We need to "guess" an invariant that both
    (i) is satisfied before the loop runs
    (ii) is preserved by the loop
    (iii) is strong enough to prove what we want after the loop

    ^^^^^ Loop invariant == conditions (i)-(iii) above!

    Dafny will verify that all of (i), (ii), (iii) is true.
    It will not allow you to pick an invariant that's wrong.

    NOTE: (i), (ii), and (iii) are not quite the same as the informal
    characterization above! (In fact, they are stronger.)
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
        // After a while loop, Dafny isn't sure what's true or not - so
        // it uses the invariant we wrote and forgets everything else!

        return curr;
    }
}

/*
    ===== Exercise =====

    Here's a very inefficient version of a function
    that copies a nonnegative integer.

    Let's write a loop invariant that will allow us to prove CopyInt.

    Remember, a loop invariant must be:
    (i) true before entering the loop,
    (ii) preserved by the loop body
    (iii) imply the postcondition after the loop ends
*/

method CopyInt(a: nat) returns (b: nat)
    // Uncomment to try the example
    // requires a >= 0 // (technically redundant as a: nat)
    // ensures b == a
{
    var i: nat := a;
    b := 0;
    while i > 0
        // TODO: add invariants here
    {
        i := i - 1;
        b := b + 1;
    }
    // What do I know here?
}

/*
    ===== Recap and precise definition of conditions (i)-(iii) =====

    Definition:
    A loop invariant is any formula satisfying conditions (i)-(iii).

    More precisely:

    Given a loop

        // precond
        while cond {
            BODY;
        }
        // postcond

    A loop invariant is a condition Inv such that:

        (i) Inv is true before executing the loop -- implied by the precondition

        (ii) Inv is preserved by the loop: on *any* state satisfying

                Inv && while cond,

            after executing the loop, Inv holds;

            (NOTE: this is not the same as simply being true after each iteration of the loop!)
            (think of this as pulling BODY out as its own program with a pre/postcondition.)

        (iii) Inv && !cond implies the postcondition.

    A few points:

    1. This is not the same as saying that the formula is true before executing, and after every loop iteration!
        (see above)

        --> However, any loop invariant will be true before executing the loop and after each iteration!

        --> It will also be true at the start of the loop. (But not necessarily during the middle of the loop body)

    2. Notice that conditions (ii) and (iii) involve the while loop condition cond.

    3. For condition (ii), think of it as pulling the while loop body out of the loop, and popping it into its own
        method with a pre/postcondition

            This is how loop invariants can be used to reduce the verification

    4. For condition (iii): Dafny forgets about all information following the loop unless it's explicitly stated
       in the invariant!

            Often, we have to be very explicit in Dafny when writing loop invariants!

            Loops are the thing Dafny doesn't bother to solve automatically - Dafny asks for our help.

    5. It will turn out that this is enough to verify all real-world programs: we have reduced the verification
        of programs involving loops to those not involving loops!
        From there, Dafny can just do the weakest precond / strongest post calculations automatically,
        as in part 2.

*/

// Another example for the following poll
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
    ===== Poll =====

    Consider the AddOne method above.

    Which of conditions (i), (ii), and (iii) is satisfied by each of the following
    possible invariants?

    1. b > 0
    2. b >= 0
    3. b < a + 1
    4. b <= a + 1
    5. b == a + 1
    6. a + 1 < b <= 2 * a
    7. b >= 100

    https://forms.gle/76wZFH4mBcq79bQq6

    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
    .
*/

/*
    ===== Sequences =====

    Loops and invariants become especially useful when working
    with more complex data types, like sequences.
    Let's give an overview of these.

    A sequence is basically a list. To create a new sequence:

        b := [];
        b := [1, 2, 3];

    On your homework, there are a few questions about sequences.

    Sequences are immutable.
    Dafny supports sequences seq<int> and imperative arrays array<int>,
    which are mutable. We won't use arrays on the homework.
*/

method Find(a: seq<int>, key: int) returns (index: int)
    // Uncomment to try
    // ensures 0 <= index < |a| ==> a[index] == key
    // ensures index == |a| ==> forall k :: 0 <= k < |a| ==> a[k] != key
{
    // Can we write code that satisfies the postcondition?
    index := 0;
    while (index < |a|) && (a[index] != key)
        // TODO: add invariants here
    {
        index := index + 1;
    }
    // We know that index == |a| OR a[index] == key
    // We know that forall k :: 0 <= k < |a| ==> a[k] != key
}

// SKIP: a similar example
// Find the maximum element in a sequence
// method FindMax(a: seq<int>) returns (max_i: int)
//        requires a.Length > 0
//        ensures 0 <= max_i < a.Length
//        ensures forall k :: 0 <= k < a.Length ==> a[max_i] >= a[k]
// {
// }
