/*
    Lecture 4, Part 3:
    Strongest postconditions and weakest preconditions

    ===== Overview =====

    We saw that in order to prove properties about
    methods like Abs and Double,
    we needed to strengthen the postcondition to be stronger
    (or use a function instead of a method.)
    Is the new postcondition really as strong as it can be?

    For example, for Double:

        Is ensures y == x + x really the strongest possible?

    We will see that the answer is yes: this is in a formal
    sense, the strongest possible statement about the output.

    Recall: Full functional correctness:
    - A **full functional correctness spec** exactly specifies what the output
      is for each input.
    - See HW1, part 1B (and a question on the midterm)
    - Think of it as: check/verify every piece of data in the output is as intended

    Strongest postconditions can be used to define this a little more formally,
    but also, both strongest postconditions and weakest preconditions will be
    useful to give a fully automated (or algorithmic) way to calculate strong
    specs for any function. We will see that this is roughly how Dafny works
    internally.

    Sneak peak: along the way, we'll see some useful techniques for writing/debugging
    Dafny code with assertions that will be very useful later on.

    ===== Definitions =====

    Let's define:

    - Going forwards:
        Given a precondition and a statement (or program),
        the *strongest postcondition* is the strongest property
        that is guaranteed to hold after executing the statement (or program)
        (assuming that the precondition holds).

        **Important:** (Addendum after discussion on 3/5):
        We conventionally include both the input variable(s) and output variable(s)
        when defining strongest postconditions:
        so if f(x) = y, it is a statement on both x and y.

        Sometimes written:

            SP(MyProg, pre) = post

    - Going backwards:
        Given the postcondition,
        the *weakest precondition* of a statement (or program) is the weakest condition
        that guarantees that the postcondition will hold after executing the statement.

        Unlike the SP, the weakest precondition is conventionally given only on the
        input variables (since the output is not known yet!)
        So if f(x) = y, it is a statement on x only.

        Sometimes written:

            WP(MyProg, post) = pre

    Why weakest?
    - We want as few constraints on the input as possible
    - We want to test/verify as many inputs as possible for the function to work
        (verifying more inputs == stronger spec)

    Another way of seeing it:
    - Stronger postcondition ==> stronger spec
    - Weaker precondition ==> stronger spec

    (Q: What would be the weakest postcondition for any program MyProg?
        It would just be true
    Q: What would be the strongest precondition for any program MyProg?
        It would just be false.
    So both of these are not useful.)

    Here are some examples based on the abs function:
*/

// include for abs()
include "2-abstraction.dfy"

method StrongestPostconditionEx(x: int) returns (y: int)
    requires x >= 5
    // What ensures statement should go here?
    // We know that y is equal to exactly abs(x+x) ...
    ensures y == abs(x + x)
    // We can also say other things...
    // Do we need the following?
    // A: Yes! (part of the strongest possible postcondition)
    // - Even though: not necessary to state in Dafny as they are know to be true before the program executes,
    // and Dafny knows that the input was not modified, so they remain true afterwards.
    // - See discussion below.
    //
    // We also know that x >= 5. (This was true before
    // executing the function, so it remains true after.)
    ensures x >= 5
    // That also implies more information about the output y:
    ensures y >= 10
{
    y := abs(x + x);
}

// method TestStrongestPostconditionEx() {
//     var x := 5;
//     var y := StrongestPostconditionEx(x);
//     assert y == 10;
// }

// method TestStrongestPostconditionEx2(x: int) {
//     if x >= 5 {
//         var y := StrongestPostconditionEx(x);
//         assert x >= 5;
//         assert y >= 10;
//     }
// }

method WeakestPreconditionEx(x: int) returns (y: int)
    // What requires statement should go here?
    requires x <= -5 || x >= 5
    // requires false // Replace this line
    ensures y >= 10
{
    y := abs(x + x);
}

/*
    A few points:

    1. Strongest postcondition and weakest precondition are not always inverses!

        For example, in this program, if we start from the postcondition y >= 10, and go to the WP,
        we will get x <= -5 || x >= 5; if we forwards again though we get
        (x <= -5 || x >= 5) && abs(x + x) == y,
        which is stronger than before.

    2. Strongest postcondition depends on the set of variables that are in scope.

        By convention: x, y in scope for a program for postcondition; x only for a precondition

        In the context of a larger program: depends on the scope in each block!

    3. Strongest postcondition is NOT the same as the maximum information that we need to state in Dafny

        + In fact, it is actually the maximum information that is *inferred* internally by Dafny,

        + We may need to restate information known about the input (i.e. restate preconditions
          in the strongest postcondition) to get the strongest possible statement about the output),

        + Typical case: (strongest postcond) = precond && (Dafny postcond)

    4. Multiple strongest postconditions (or weakest preconditions) may be possible, as long as they are
      logically equivalent; i.e. for post1 and post2

            z3.prove(z3.Implies(post1, post2)) == PROVED
            z3.prove(z3.Implies(post2, post1)) == PROVED

        Example:

            y == abs(x + x) && x >= 5

            equivalent to

            y == abs(x + x) && x >= 5 && y >= 10

    ===== Poll =====

    Consider the following method:

    method Birthday(age: int) returns (new_age: int)
    {
        return age + 1;
    }

    1. If the precondition is

        age >= 0

    then what is the strongest postcondition?

    2. If the postcondition is

        new_age == age + 1 && new_age >= 0

    then what is the weakest precondition?

    https://forms.gle/qYdirit7qtvJFB9KA

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

    Valid answers for #1:

        new_age == age + 1 && age >= 0
        new_age == age + 1 && new_age >= 1

        Note:

            new_age == age + 1

        is not enough! Go back to the definition from above:

            Strongest Postcondition should be the strongest possible property that is
            guaranteed to hold after executing the program.

        Based on this definition (think in Python for example)

            After executing the program, we know that new_age == age + 1, but we also still
            know that age >= 0 (or equivalently, new_age >= 1).

            To specify the strongest postcondition, we should include one of these two statements.

    Valid answers for #2:

        age >= -1 (or logically equivalent, e.g. age + 1 >= 0)

        - "true" is weaker, but not satisfied by this program

        - "age >= 0" is satisfied, but not the weakest possible.

    ===== Testing it out =====
*/

method birthday(age: int) returns (new_age: int)
    // 1. SP(age >= 0)
    // requires age >= 0
    // ensures age >= 0 && new_age == age + 1
    // ensures new_age >= 1 && new_age == age + 1
    // 2. WP(new_age == age + 1 && new_age >= 0)
    // requires age >= -1
    // ensures new_age == age + 1 && new_age >= 0
{
    return age + 1;
}

/*
    Another definition:

    SP(MyProg, pre):

        Describe (the set of) all input output pairs (x, y) such that
        running the method on an input state x satisfying
        pre may produce output y

    WP(MyProg, post):

        Describe (the set of) all input states x such that running
        the method on input x produces an output y satisfying post

    The set of: emphasize there may be zero or more than one.

    === Computing strongest postconditions and weakest preconditions ===

    How do we actually compute these things?

    At every point in your program, write down exactly
    everything that is known to be true about the state of the program
    at that point!

        This is a more general debugging technique in Dafny!

        Querying what Dafny knows/doesn't know is often useful.

    To do strongest postconditions: work forwards.
    To do weakest preconditions: work backwards.

    ===== Working forwards: =====
*/

method StrongestPostconditionEx2(x: int) returns (y: int)
    requires x >= 5
    // TODO: what ensures statement should go here?
    // Let's figure it out!
    // ensures ...
    ensures (
        (x >= 5 && x <= 10 && y == abs(x + x + x))
        ||
        (x >= 11 && y == abs(x + x))
    )
    // Simpler way to write this?
    ensures x >= 5
    ensures x >= 5 && x <= 10 ==> y == 3 * x
    ensures x >= 11 ==> y == 2 * x
{
    // What we know to be true at this point?
    assert x >= 5;

    if x <= 10 {

        // What do we know to be true at this point?
        assert x >= 5 && x <= 10;

        y := abs(x + x + x);

        // What do we know to be true at this point?
        assert x >= 5 && x <= 10 && y == abs(x + x + x);
        // we could add other statements...
        // assert y >= 15;
        // assert y <= 30;
        // ^^ logically implied by the above, so not needed

    } else {

        // What do we know to be true here?
        assert x >= 11;

        y := abs(x + x);

        // What do we know to be true here?
        // assert x >= 11 && y == abs(x + x) && y >= 22;
        // also sufficient:
        assert x >= 11 && y == abs(x + x);

        // Would this be sufficient:
        // assert y == abs(x + x) && y >= 22;
        // No - that allows x <= -11

        // Also sufficient:
        // assert x >= 11 && y == x + x;
    }

    // Interesting part: what ends up being true here?
    // What do we know to be true?
    // Use OR.
    assert (
        (x >= 5 && x <= 10 && y == abs(x + x + x))
        ||
        (x >= 11 && y == abs(x + x))
    );

    // That's it -- we have (mostly mechanically)) calculated the SP given the precondition.
    // Let's check that it worked
}

/*
    ===== Working backwards: =====

    (We will go through this one already filled)
*/

// The working backwords method!
method WeakestPreconditionEx2(x: int) returns (y: int)
    // TODO: uncomment
    ensures y >= 5
    // TODO: what requires statement should go here?
    // Let's figure it out!
    // What we get with the automatic "working backwards" method:
    // requires (
    //     x <= 10 ==> (x >= 2 || x <= -2)
    // )
    // requires (
    //     x > 10 ==> (x >= 3 || x <= -3)
    // )
    // Simplied (logically equivalent):
    requires x <= -2 || x >= 2
{

    // What does Dafny need to be true here?
    assert (
        x <= 10 ==> (x >= 2 || x <= -2)
    );
    assert (
        x > 10 ==> (x >= 3 || x <= -3)
    );

    if x <= 10 {
        // What does Dafny need to be true here?
        assert x >= 2 || x <= -2;

        // Equivalently (!)
        // What happened here?
        assert abs(x + x + x) >= 5;

        y := abs(x + x + x);

        // What does Dafny need to be true here?
        assert y >= 5;
    } else {
        y := abs(x + x);

        // What does Dafny need to be true here?
        assert y >= 5;
    }

    // What does Dafny need to be true here?
    assert y >= 5;
}

/*
    ===== Conclusion and Segue =====

    You can think of Dafny as doing both of these steps internally, whenever
    it verifies programs!
    (I.e., under the hood: Dafny is calculating weakest preconditions and strongest postconditions
    automatically)

    How?
    Pseudocode: For each program Prog with postcondition post:

        - Calculate WP(Prog, post)

        - Check that pre ==> WP(Prog, post) (query to Z3!).

    (Weakest preconditions work a little better than strongest postconditions for this purpose,
     for reasons we will not get into.)

    This works great!
    But there is one problem.

    What is missing from our discussion so far?

    A:
*/
