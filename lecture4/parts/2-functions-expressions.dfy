/*
    Lecture 4, Part 2:
    Functions and expression

    Two main concepts:
    - Function/method distinction
    - Weakest preconditions and strongest postconditions

    ===== Poll =====

    Consider the following Double method:
*/

// Import from part 1
include "1-intro.dfy"

method Double(x: int) returns (y: int)
    // requires ... ensures ...
    // requires false // this function cannot be called
    // ensures false // this function never returns
    ensures y == x + x
{
    y := x + x;
}

// Which of the following pre/postconditions can we add
// to get both the method and the following test to pass?

method TestDouble()
{
    var x := Double(4);
    assert x == 8; // Uncomment this line
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

    (After poll: try it out)
*/

/*
    ===== Functions =====

    Last time, we saw that we can't prove that Abs(5) == 5
    unless we give it a strong postcondition.
    This same problem occurs with options (1) and (2) above
    (Double(5) == 10):
    (Why?)

    The reason? *Abstraction:* A Dafny method is "opaque":
    considered abstracted by only its pre/postcondition behavior.

    There is an easier way:
    Dafny allows us to define mathematical functions
    that are not opaque when the Dafny verifier runs:
*/

function abs(x: int): int
{
    // Syntax looks a bit different: this is
    // mathematical expression syntax. Mathematical expressions
    // are also what appears in assert() statements and in pre/postconditions.
    if x >= 0 then x else -x
}

method TestAbsEasier()
{
    assert abs(5) == 5; // passes
    assert abs(-4) == 4; // passes
}

/*
    Functions expose another important concept in Dafny:
    only functions can be used in expressions!
    Methods cannot be used in expressions.

    (We ran into this problem last time!)

    What happens when we try to call AbsFixed(5) in an expression?
    What happens when we try to call abs(5) in an expression?
*/

method TestAbsExpression()
{
    var x := AbsFixed(5); // This is fine
    // assert AbsFixed(5) == 5; // Error
    assert x == 5; // This passes
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

    Methods represent procedures: they can have side effects (something that happens
    when you run the function besides its input/output behavior), and can return different
    results on the same input (in theory).
    For example, it might have some state or mutate some variables.

    That means that it's not a valid thing to use in an assertion.
    Why?
    An assertion represents a statement that something is true about the state
    of your program at a given point in time.
    It would be very concerning if simply "evaluating" that assertion, changed
    whether or not it was true.

    Pragmatically speaking: you just have to remember that methods are different
    from functions and implemented separately, and only functions can be used
    in expressions.

    Recap:
    We've already learned the basics of verifying simple Dafny code!
    Methods (and tests), functions, expressions, preconditions, postconditions,
    and assert/assume.

    (One big thing missing: we haven't looked at loops or recursive functions!)

    Before we continue with more complex examples,
    I have a couple of digressions to make.
*/

/*
    ===== Digression 1: Running the code? =====

    You may have noticed something odd: we haven't run any code yet!
    In fact, even in our Tests, all we did was ask Dafny to verify that the test
    would pass.
    We only compiled the code, we didn't run it!

    But that doesn't mean Dafny can't run the code!

    Dafny is a *verification-aware* programming language.
    That means, it can verify your code, but it can also compile/run it!

    To run the code, we just need a Main() function:
*/

method Main()
{
    var x: int := -5; // Type annotation is optional
    var y: int := Abs(x);
    // assume x    == 0; // Uncomment to raise a warning about a bad assumption
    print "x = ", x, ", y = ", y, "\n";
}

/*
    To run from the command line, we can use the `dafny` command.
    Here are some of the options:

    1. `dafny verify lecture.dfy` -- to run the verifier only.
            This is equivalent to what we've been doing so far (checking the green
            bar on the left in VSCode).

    2. `dafny build lecture.dfy` -- to compile to a library, dafny.dll
         (This is also run by default with `dafny lecture.dfy`)
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
//     var x : Tree := Node(Node(Empty, 1, Empty), 2, Empty);
//     print "x=", x, "\n";
// }

/*
    There's also a fourth option to run Dafny!
    Perhaps you remember from last time, that one of the advantages of Dafny
    is that it can produce output in other languages, so it can integrate
    with your existing workflow.
    Try this:

    4. `dafny build --target:py lecture.dfy`

    This produces output in: lecture-py/module_.py.
    You can run the code with

    ```
    python3 __main__.py
    ```

    (You can ignore the other files.)
*/


/*
    ===== Digression 2: strongest postconditions and weakest preconditions =====

    We saw above that in order to prove properties about
    methods like Abs and Double,
    we needed to strengthen the postcondition to be stronger
    (or use a function instead of a method.)
    Is the new postcondition really as strong as it can be?

    Is ensures y == x + x really the strongest possible?

    We will see that the answer is yes: this is in a formal
    sense, the strongest possible statement about the output.

    On HW1, part 1B, you were asked to write specifications that are the
    *strongest possible* description of what the function does.
    What does that mean?

    We will define this in the next part.
*/
