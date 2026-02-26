/*
    Lecture 4, Part 3:
    Strongest postconditions and weakest preconditions

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

    The set of: just to emphasize there may be
    zero or more than one.

    input states/output states: we want to describe
    all variables in scope at input/output to the
    program, respectively.
    For the final: what variables are in scope
    will be mentioned.

    How do we actually compute these things?

    At every point in your program, write down exactly
    everything that is known to be true about the state of the program
    at that point.

    To do strongest postconditions: work forwards.
    To do weakest preconditions: work backwards.
*/

// What about this? (A harder one)
method StrongestPostconditionEx2(x: int) returns (y: int)
    requires x >= 5
    // TODO: what ensures statement should go here?
    // Let's figure it out!
    // What Dafny would do internally
    // ensures (
    //                     (5 <= x <= 10 && y == 3 * x)
    //                     ||
    //                     (x > 10 && y == 2 * x)
    //                 )
    // What we might come up with by hand
    ensures 5 <= x
    ensures (5 <= x <= 10) ==> y == 3 * x
    ensures (x > 10) ==> y == 2 * x
    // The two are equivalent.
{
    // What is true here?
    assert x >= 5;

    if x <= 10 {
        // What is true here?
        assert x >= 5 && x <= 10;

        y := abs(x +    x + x);

        // What is true here?
        assert x >= 5 && x <= 10 && y == abs(x + x + x);
        // Simplify (optional)
        assert 5 <= x <= 10 && y == x + x + x;

    } else {
        // What is true here?
        assert x >= 5 && x > 10;
        // Simplify (optional)
        assert x > 10;

        y := abs(x + x);

        // What is true here?
        assert x > 10 && y == abs(x + x);
        // Simplify
        assert x > 10 && y == x + x;

    }
    // What is true here?
    // What do we do at the end of an if block?
    assert (
            (5 <= x <= 10 && y == x + x + x)
            ||
            (x > 10 && y == x + x)
        );

    assert (
            (5 <= x <= 10 && y == 3 * x)
            ||
            (x > 10 && y == 2 * x)
        );

}

// The working backwords method!
method WeakestPreconditionEx2(x: int) returns (y: int)
    // TODO: uncomment
    ensures y >= 5
    // TODO: what requires statement should go here?
    // Let's figure it out!
    // What Dafny would come up with automatically
    requires (
                         x <= 10 ==> abs(x + x + x) >= 5)
                     &&
                     (x > 10 ==> abs(x + x) >= 5
                     )

{

    assert (
            (x <= 10 ==> abs(x + x + x) >= 5)
            &&
            (x > 10 ==> abs(x + x) >= 5)
        );

    if x <= 10 {
        assert abs(x + x + x) >= 5;

        y := abs(x +    x + x);

        assert y >= 5;
    } else {
        // Evaluate the assignment y := abs(x + x)
        // in reverse!
        assert abs(x + x) >= 5;

        y := abs(x + x);

        assert y >= 5;
    }
    assert y >= 5;
}

/*
    Strongest postconditions and weakest preconditions are a key part of how
    Dafny works internally -- it is calculating them implicitly all the time!

    The way it does it is basically the process we did above.
    It can be done in a completely automatic way, just like with Z3.

    This works great!
    But there is one problem with.

    Any guesses - what is missing from our discussion so far?

    A:
*/
