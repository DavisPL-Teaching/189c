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

    Strongest postconditions and weakest preconditions can be used to give a formal
    definition of what we mean by full functional correctness.

    Sneak peak: along the way, we'll see some useful techniques for writing/debugging
    Dafny code with assertions that will be very useful later on.

    ===== Definitions =====

    Let's define:

    - Going forwards:
        Given a precondition,
        the *strongest postcondition* of a statement (or program) is the strongest property
        that is guaranteed to hold after executing the statement (or program)
        (assuming that the precondition holds)

        Sometimes written:

            SP(MyProg, pre) = post

    - Going backwards:
        Given the postcondition,
        the *weakest precondition* of a statement (or program) is the weakest condition
        that guarantees that the postcondition will hold after executing the statement.

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
    // BELOW:
    // - part of the strongest possible postcondition, but not necessary
    // to state in Dafny as they are know to be true before the program executes,
    // and Dafny knows that the input was not modified, so they remain true afterwards.
    // - In general, if the input is modified or we are in some other language, we might
    //   want to include this information in the postcondition, so it is part of the strongest postcondition.
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

    - It could be that after taking the strongest postcondition, and going backwards to the weakest precondition,
      we might end up with a different precondition that we started.

      ^^^^^ Q about this - will revisit & post after class

    - Multiple strongest postconditions (or weakest preconditions) may be possible, as long as they are equivalent;

    - We may need to restate information known about the input (i.e. restate preconditions in the strongest postcondition) to get the strongest possible statement about the output

        + Even though sometimes this information would be known to Dafny
        + May not be known/guaranteed in some other language like Python, and is not logically equivalent.

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

    Answer for #1:

        new_age >= 1
        new_age == age + 1
        age >= 0 && new_age >= 1
        both first and second

        Interesting question:

        is:
            new_age == age + 1

        enough, or do we need:

            age >= 0 && new_age == age + 1

            new_age >= 1 && new_age == age + 1

        Clearing things up...

        These would not be needed in Dafny, because Dafny already knows that age >= 0
        from before the method call.

        However, let's take a look at the definition:

            Strongest Postcondition should be the strongest possible property that is
            guaranteed to hold after executing the program.

        Based on this definition (imagine in Python for example)

            After executing the program, we know that new_age == age + 1, but we also still
            know that age >= 0 (or equivalently, new_age >= 1).

            To specify the strongest postcondition, we should include one of these two statements.

        Revise our discussion from earlier:

            1. The strongest postcondition, by definition and
                for the purposes of this class (and in general),
                includes all possible statements that we know to be true
                after executing the program,
                (even including statements about the input)

            2. In Dafny, we may not need to re-state properties about the input,
               as Dafny will have carried them over from the precondition
               and still knows them to be true (as long as the input was not modified).

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
    StrongestPostcondition(P):

        Describe (the set of) all input output pairs (x, y) such that
        running the method on an input state x satisfying
        P may produce output y

    WeakestPrecondition(Q):

        Describe (the set of) all input states x such that running
        the method on input x produces an output y satisfying Q

    The set of: emphasize there may be zero or more than one.

    input states/output states: we want to describe
    all variables in scope at input/output to the
    program, respectively.
    For the final: what variables are in scope
    will be mentioned.

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

// What about this? (A harder one)
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
*/

// The working backwords method!
method WeakestPreconditionEx2(x: int) returns (y: int)
    // TODO: uncomment
    // ensures y >= 5
    // TODO: what requires statement should go here?
    // Let's figure it out!
    // requires ...
{

    if x <= 10 {
        y := abs(x +    x + x);
    } else {
        y := abs(x + x);
    }
}

/*
    ===== Recap and conclusions =====

    Strongest postconditions and weakest preconditions are a key part of how
    Dafny works internally -- it is calculating them implicitly all the time!

    The way it does it is basically the process we did above.
    It can be done in a completely automatic way, just like with Z3.

    (In fact, Dafny uses Z3 under the hood.)

    This works great!
    But there is one problem with the above.

    What is missing from our discussion so far?

    A:
*/
