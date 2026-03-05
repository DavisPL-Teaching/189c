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
    - see HW1, part 1B

    Strongest postconditions and weakest preconditions are related!

    ===== Definitions =====

    Let's define:

    - Going forwards:
        Given a precondition,
        the *strongest postcondition* of a statement (or program) is the strongest property
        that is guaranteed to hold after executing the statement
        (assuming that the precondition holds)

        Sometimes written:

            SP(MyProg, pre) = post

    - Going backwards:
        Given the postcondition,
        the *weakest precondition* of a statement (or program) is the weakest condition
        that guarantees that the postcondition will hold after executing the statement.

        Sometimes written:

            WP(MyProg, post) = pre

    Here are some examples based on the abs function:
*/

// include for abs()
include "2-abstraction.dfy"

method StrongestPostconditionEx(x: int) returns (y: int)
    requires x >= 5
    // What ensures statement should go here?
    ensures y == abs(x + x)
    ensures y >= 10
    ensures x >= 5
{
    y := abs(x + x);
}

method WeakestPreconditionEx(x: int) returns (y: int)
    // What requires statement should go here?
    // requires false // Replace this line
    requires x >= 5 || x <= -5
    ensures y >= 10
{
    y := abs(x + x);
}

/*
    ===== Poll =====

    Consider the following method:

    method birthday(age: int) returns (new_age: int)
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

    ===== Testing it out =====
*/

method birthday(age: int) returns (new_age: int)
    // 1. SP(age >= 0)
    // requires age >= 0
    // ensures age >= 0 && new_age == age + 1
    // 2. WP(new_age == age + 1 && new_age >= 0)
    // requires age >= -1
    // ensures new_age == age + 1 && new_age >= 0
{
    return age + 1;
}

/*
    Another definition:
    StrongestPostcondition(P):

        Describe (the set of) all output states y such that
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
{
    if x <= 10 {
        y := abs(x +    x + x);
    } else {
        y := abs(x + x);
    }
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
