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

// Here is the simple Dafny program corresponding to python/Z3 abs:

method Abs(x: int) returns (y: int)
    ensures y >= 0 // <-- specification! (postcondition)
    // Uncomment to see red squigglies / counterexample
    // ensures y == 0
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

    - "Methods" are functions in other languages.

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
    // requires x == 0
    ensures y >= 0
{
    if x >= 0 {
        // return x;
        y := x;
    } else {
        y := -x;
    }
}

/*
    ===== Preconditions and postconditions =====

    We use `requires` to indicate a precondition, and
    `ensures` to indicate a postcondition.

    If we modify the code to do something wrong,
    Dafny will catch the error:
    - modifying ensures to a postcondition that is wrong?
    - modifying the return value to return -1 (e.g.)?
    - modifying requires to a precondition that is wrong?

    Summary: Dafny checks whether the spec holds:
    - for *all* inputs satisfying the precondition, after the program
        is run, the output satisfies the postcondition.

    Q: is requires like assume() in Hypothesis?

        Yes, you can think of it that way.

    Some design questions:

        Q1: Why are return values (like y) named?

        Q2: Why are values (like x and y) typed?

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

    As we learned with Hypothesis, preconditions and postconditions can
    be thought of as special cases of assumptions and assertions.

    What assumptions and assertions might we want to add to Abs?
*/

method Abs3(x: int) returns (y: int)
    ensures y >= 0
{
    // Uh oh...
    // assume{:axiom} false;

    if x >= 0 {
        y := x;
        // What assertion could we check here?
        assert y == x;
    } else {
        y := -x;
        // What assertion could we check here?
        assert y == -x;
        // What assumption + assertion could we add here?
        // assume{:axiom} x == -3;
        // assert y == 3;
        // // What else?
        // assume{:axiom} x == -2;
        // // what happens here?

        // // The code is unreachable here...
        // assert false;

        // return 100;

        // assert false; // unreachable
        // ^ Assume is dangerous!
    }
}

// There is one important way that assume/assert are different in Hypothesis and Dafny!

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
    Quick recap:

    We talked about interactive formal verification and its advantages

    We talked about conditions when it's worth investing in the extra effort
    for interactive verification (correctness is critical, security, & high financial cost)

    We introduced Dafny syntax and saw the beginnings of writing code & proofs together in
    the same language (i.e. verification language + programming language)
    - methods
    - basic syntax (if then else, assignments, etc.)
    - preconditions (requires) postconditions (ensures)
    - return statements / multiple returns
    - assume{:axiom} (very dangerous) and assert, which are erased from the code after verification passes.
*/

/*
    ===== Mini-exercise =====

    Implement a Max function that returns the maximum of three integers,
    and write pre- and post-conditions for it.

    TODO list:
    1. Implementing the function
    2. Write pre/postconditions
    3. Verify it (check that it's working)
    4. Test it (write unit tests - we'll talk more about why these are useful)
*/

method Max(a: int, b: int, c: int) returns (result: int)
    // Placeholder - makes the function a "stub"
    // Precondition
    // requires false
    // What postcondition should go here, so that the function operates as expected?
    ensures result == a || result == b || result == c
    ensures result >= a && result >= b && result >= c
{
    if a > b {
        if a > c {
            return a;
        } else {
            // if b > c {
            //     assert false;
            //     return b;
            // } else {
            //     return c;
            // }

            return c;
        }
    } else {
        if b > c {
            return b;
        } else {
            return c;
        }
    }
}

// Let's test to see if our method is working!

method TestMax()
{
    // Uncomment to run
    var a: int := 5; // The 'int' annotation is optional (it is inferred)
    var b: int := 50;
    var c: int := 100;
    var y := Max(a, b, c);
    assert y == 100;

    // Note that we've "tested" the code without actually running it!
    // We will circle back to that soon as well.
}
