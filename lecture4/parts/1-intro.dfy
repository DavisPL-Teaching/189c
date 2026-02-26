/*
    Lecture 4, Part 1:
    Introduction to Dafny

    So far:
    - We gave a high-level overview of formal verification and why it matters
      (when you might want to use it for a project)
    - We saw that many formal verification tools exist -- for different languages
      and purposes. In this class, we will use the Dafny verification language.
    - Key point: Dafny is both a programming language and a verification tool.

    ===== Dafny resources =====

    Resources to keep in mind:

    - [Dafny tutorial](https://dafny.org/latest/OnlineTutorial/guide)
    - [Dafny cheat sheet](https://dafny.org/latest/DafnyCheatsheet.pdf)
    - [Reference manual and user guide](https://dafny.org/latest/DafnyRef/DafnyRef)
    - Textbook: *Program Proofs,* by Rustan M. Leino -- [link](https://mitpress.mit.edu/9780262546232/program-proofs/)

    ===== Poll =====

    Which of the following is a scenario where investing in interactive formal verification will likely be the most useful?

    https://forms.gle/XnahxmXeCpbhXBKS6

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

        Q1: Why are return values (like y) named?

        Q2: Why are values (like x and y) typed?

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
        .
        .
        .
        .
        .

        A1: So that we can refer to them in the postcondition

        A2: Dafny needs to know the type of a value to be able to
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

    Implement a Max function that returns the maximum of three integers,
    and write pre- and post-conditions for it.

    What kind of pre and postconditions would we like to have here?
*/

method Max(a: int, b: int, c: int) returns (result: int)
    // Placeholder - makes the function a "stub"
    requires false
    // What postcondition should go here, so that the function operates as expected?
    // ensures ....
{
    // TODO: fill in the code here
}

// Let's test to see if our method is working!

method TestMax()
{
    // Uncomment to run
    // var a: int := 5; // The 'int' annotation is optional (it is inferred)
    // var b: int := 50;
    // var c: int := 100;
    // var y := Max(a, b, c);
    // assert y == 50;

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
    // Fixed postcondition:
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
*/
