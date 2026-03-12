/*
    Lecture 4, Part 5:
    Conclusions

    === A problem: when assertions do not pass ===

    Consider the following snippet of a program:

        assert P;
        assert Q;

        ^^^ suppose P ==> Q is logically true, but P passes and Q fails, why might
                this be?

    This can happen!
    Sometimes, Dafny assertions do not pass.

    === Poll ===

    This is the last in-class poll!

    (Consider the snippet above)

    Suppose that P implies Q (logically) but Dafny verification passes
    only for P, and not Q.
    Which of the following is a possible reason for this? (Select all that apply)

    Assume that P and Q are syntactically correct Dafny expressions.

    A. Q is equivalent to false.
    B. P is equivalent to true.
    C. Q is equal to P, they are syntactically the same formula.
    D. The proof that arrives at Q from P uses steps that are too complicated to quickly check for a computationally bounded verifier.
    E. P and/or Q involve complex statements using quantifiers.
    F. P and/or Q involve complex statements using recursive functions or arrays.
    G. Q involves Dafny methods rather than only functions/expressions
    H. Q is true, but not provable from P.

    === Example ===

    Let's see how this can show up in practice by trying to write a unit test
    for the following function, MinList.
*/

// Here is a MinList function to calculate the minimum of a list
// It's similar to the Max function from Part 1.

method MinList(a: array<int>) returns (min: int)
    // Precondition
    requires a.Length >= 1
    // Postcondition
    // - The value min should be one of the elements of the array
    //   "There exists an index i (within correct bounds) such that a[i] == min"
    ensures exists i :: (0 <= i < a.Length) && a[i] == min
    // - The value min should be <= each element of the array.
    ensures forall i :: 0 <= i < a.Length ==> min <= a[i]
{
    min := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> min <= a[j]
        invariant exists j :: 0 <= j < i && min == a[j]
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }

    // Optional
    // return min;
}

method TestMinList2() {
    // previous test:
    var a0 := new int[][1];
    // a0[0] := 3;
    var result1 := MinList(a0);
    assert result1 == 1;

    // Try more complicated examples here.

    // New example syntax:
    var a1 := new int[][1, 2, 3, 4, 5];
    // var a1 := new int[][1, 2, 3, 4, 0];
    var result2 := MinList(a1);

    // Uncomment to try
    // assert result2 == 1;

    // Debugging?
    // Try to figure out what Dafny knows:
    // assert a1[0] == 1;
    // assert a1[1] == 2;
    // assert a1[2] == 3;
    // assert a1[3] == 4;
    // assert a1[4] == 0;

    // MissingStep(a1, result2);

    // assert result2 == 1;

    // An even simpler example :-)
    // var a2 := new int[][1, 2, 3, 4, 5];
    // assert a1 == a2;
}

// Missing step for the verification above
lemma MissingStep(
    a: array<int>,
    result: int
)
    requires a.Length > 3
    requires a[1] == 2
    requires a[2] == 3
    requires a[3] == 4
    ensures result == 1
{
    // Omit for now
    assume{:axiom} false;
}

/*
    === Dafny as a "computationally bounded verifier" ===

    Why did first unit test pass, but second unit test failed?
    Dafny is a "computationally bounded verifier"!
    Dafny is not executing the unit test, it's verifying that it's
    logically provable.
    So?
    Does Dafny even know the array is [1, 2, 3, 4, 5]?
    Evaluating the array a1 is doing computation!
    What's happening - 1 is below the length of an array that Dafny
    is willing to evaluate; 5 is above that amount.

    This is more generally, a highly productive way to view
    Dafny and what it does/does not do!
    Recall loop invariants and strongest postconditions/weakest preconditions.

    Why might Dafny give up when it sees a loop and ask the user for input?

    It's the same reason with the assertions above :-)
*/

/*
    === Tips when you get stuck ===

    Some techniques for when you get stuck on a Dafny proof.

    1. Find out what Dafny knows.

    You can query with assertions!

        assert P

      If it passes - either Dafny knows P (or Dafny did not previously
          know P, but now does)

      If it fails - Dafny does not know P.

    2. Abstract the missing step or cases
       into a lemma with a precond and postcond.

    3. Convince yourself the thing you're trying to prove is true!
       Once you are convinced, *assume* away the lemma you need (or axiom it),
       and come back to it later,
       to make the proof go through.

    The above technique will allow you to decompose any proof into smaller
    parts, and tackle each part one at a time.

    If you've simplified the property at all - you've made progress!
    That's all we need in order to guarantee we eventually complete it.
*/

/*
    === End notes ===

    What are the main advantages of Dafny?

    1. Prove arbitrary code correct
    2. Don't need to rewrite the code in verification language (executable/verifiable code in same framework)
    3. Compile & integrate with other languages

    What are the main limitations of Dafny?

    1. High effort to write and verify real-world software
    (10x estimate)
    2. Q is true, but not provable from P?

        could be: your code is actually correct, and you can't prove it!

    (1) is true, but not fundamental.
    (2) is actually possible and is more fundamental.
    This is a topic that we could get to if we cover the foundations of Dafny,
    including the foundational logics (such as first-order logic, or FOL, and Hoare logic),
    on which it is built.
*/

/*
    Finishing with a quote from the Dafny tutorial:
    https://dafny.org/latest/OnlineTutorial/guide

    Even if you do not use Dafny regularly, the idea of writing down exactly what it is that the code does is a precise way, and using this to prove code correct is a useful skill. Invariants, pre- and post conditions, and annotations are useful in debugging code, and also as documentation for future developers. When modifying or adding to a codebase, they confirm that the guarantees of existing code are not broken. They also ensure that APIs are used correctly, by formalizing behavior and requirements and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions, and writing assertions to check assumptions are all general computer science skills that will benefit you no matter what language you work in.
*/

/*
    ===== Discussion on industry applications =====

    Course goals:
    - to understand how verification works
    - to apply verification to real-word projects

    The methodology of verification:

    1. We encode the problem we are considering
      (based on real software, in a real industry application)
      in preconditions, postconditions, and other domain-specific constraints
      in an appropriate verification framework.

    2. We use the tool to prove the property, thus proving the code 100% free from bugs.

    When is this methodology useful in practice?
    Not always! But often in cases where correctness, safey, or security is critical
    to system functioning.
    Investment examples:

    - Amazon: verifying low-level cryptographic libraries using tools
      like Dafny and CBMC, verifying domain-specific security constraints
      (e.g., your cloud data cannot be accessed by untrusted users)

    - Microsoft: many applications of Z3 and other techniques internally, verifying network code,
      device and kernel drivers, etc.

    - Hardware bugs & hardware verification:

        Pentium FDIV bug: affected Intel Pentium processors in 1994.
        recall of all defective Intel processors at the time
        $475 million in losses!

    - Signal messaging app: verification effort for core messaging protocol going back to 2017

    - Larger-scale realistic software projects coming from academia:
        CompCert: a verified optimizing C compiler
        CertiKOS: a verified operating system kernel
        Increasing interest from the systems community and more work every year on building
        bigger verified file systems, network controllers, etc.

    - More generally, at large industry scale, security bugs cost a LOT of money.
      Higher-ups will throw money at any technique which even has a chance of preventing large-scale
      security risks (willing to invest).

    - The argument is that despite a much greater effort, we also get a greater payoff.
      Verify your library ==> greater assurance against threats, more people want to use it,
      maintain the verification conditions on all future software updates
*/
