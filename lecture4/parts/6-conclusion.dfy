


/*
    What are the main advantages and limitations of Dafny?

    - Invariants are very difficult to figure out (even for a human!) and very
        effort intensive

    - It inherits some of the same limitations of Z3
        + If Z3 returns unknown or times out, Dafny also doesn't know what to do
        + This is exactly what makes verification sometimes so difficult: we need
            to add more information to help Dafny get through the assertion and give
            it enough information to pass to Z3 so that Z3 knows the assertion is true.
        + This is actually both a benefit and a drawback, as unlike
            with Z3 where it can be unclear what additional information
            to add to get the proof to work (we saw this somewhat in HW3),
            with Dafny we at least know that we can add some additional
            information to eventually get the proof to go through.

    Summary:
        - A lot more expressive and general; but
        - A lot more effort intensive to get the proofs to go through.
*/

/*
    Finishing with a quote from the Dafny tutorial:
    https://dafny.org/latest/OnlineTutorial/guide

    Even if you do not use Dafny regularly, the idea of writing down exactly what it is that the code does is a precise way, and using this to prove code correct is a useful skill. Invariants, pre- and post conditions, and annotations are useful in debugging code, and also as documentation for future developers. When modifying or adding to a codebase, they confirm that the guarantees of existing code are not broken. They also ensure that APIs are used correctly, by formalizing behavior and requirements and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions, and writing assertions to check assumptions are all general computer science skills that will benefit you no matter what language you work in.
*/
