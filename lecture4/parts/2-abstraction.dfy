/*
    Lecture 4, Part 2:
    Abstraction

    ===== Overview =====

    We've learned about basic Dafny syntax and Dafny methods.

    Let's talk more about how Dafny works, and the power
    of abstraction.
    Starting with a mini-exercise.

    Some upcoming concepts:
    - Interfaces & abstraction; writing unit tests
    - Function/method distinction
    - Compile time/runtime distinction
    - Weakest preconditions and strongest postconditions
*/

include "1-intro.dfy"

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
    to verify the assertion, but rather uses the knowledge that it has from Abs' specification.

    What's left of the method is only the pre and postconditions!

    This is a common scenario in formal verification: it often happens
    that the verifier doesn't have enough information to prove a property.
    And, we need to strengthen the model by making the postcondition stronger.

    What postconditions should we add to Abs to fix it?
*/

method AbsFixed(x: int) returns (y: int)
    // Fixed postcondition:
    ensures y >= 0
    // The interface is complete! The contract fully specifies
    // what the output should be on every input.
    // TODO: fill in below: ...
    // ensures ...
{
    if x >= 0 {
        y := x;
    } else {
        y := -x;
    }
}

method TestAbsFixed()
{
    // ... after uncommenting this unit test
    // var x := AbsFixed(5);
    // assert x == 5;
}

/*
    However, our spec now describes exactly the body of the method, which is a bit redundant.

    That's what functions are for!
*/

/*
    Before we get to functions, today's poll.

    ===== Poll =====

    Consider the following Double method:
*/

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

    Above, we saw that we can't prove that Abs(5) == 5
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
    // Uncomment to check if the tests pass
    // assert abs(5) == 5;
    // assert abs(-4) == 4;
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
    // var x := AbsFixed(5); // This is fine
    // // assert AbsFixed(5) == 5; // Error
    // assert x == 5; // This passes
    // var y := abs(5); // This is fine
    // assert abs(5) == 5; // This is fine
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

    (One big thing missing: we haven't looked at loops or recursive functions!)
*/

/*
    Finally, let's talk about compile time vs. runtime.
    AKA: how do actually we run the code?

    ===== Running the code? =====

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
    Recap:

    - We learned about abstraction in Dafny: abstraction via preconditions/postconditions

    - How to write tests to verify the spec we wrote is strong enough.

    - Function/method distinction:
        "methods are opaque, functions are transparent"

    - Compile time vs. runtime distinction;
        how to run the code

    - We will continue with more Dafny features next time!
*/
