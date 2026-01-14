"""
Lecture 1, Part 2:
Stronger and weaker specifications

=== Intro ===

Recap: we know about
    - spec: a true or false property of a program
    - Python assertions are specifications!
    - Hypothesis: a tool for writing and testing specifications
    - Testing vs. verification

Methodology:

1. We write a program
    (i.e.: what the program does)

2. We write a specification (or spec)
    (i.e.: what the program *should* do)

3. We check whether the program satisfies the spec

    3 Methods:
    a. Testing (Hypothesis) - try random examples
    b. Automated Verification (Z3) - automatically search for a mathematical proof
    c. Interactive Verification (Dafny) - write the proof yourself

    (And other methods we won't cover in this class!
     Though I note that many other methods can be thought of as special cases of the above.
     E.g.: fuzzing = (a), static analysis = (b), typechecking = (b) and (c), etc.)
"""

# Imports
import pytest
from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

"""
Let's practice this.
(This time with a simpler example)

Exercise:

    Write a function that calculates
    the "integer square root" -- that is, takes an integer
    and calculates the square root of it, rounded down to the nearest
    integer.

    int_sqrt(4) = 2
    int_sqrt(6) = 2
    int_sqrt(9) = 3
"""

# We might need this
from math import sqrt

# 1. Write the program
def integer_sqrt(n):
    # Suggestions:
    # can we use a sqrt function?
    return int(sqrt(n))

    # Other methods:
    # - we could use a binary search on n to find the "largest" integer x
    #   x * x <= n

# 2. Write the specification - first in English
# What does it mean for this program to be correct?

# Ideas:
# - we should return an integer
# - it should return the largest integer x such that x * x <= n
#   and (x + 1) * (x + 1) > n
# Simplify?
#   we don't really need the second case, we could just say
# - it should return the largest integer x such that x * x <= n
# Another possible spec:
# - Should return int(sqrt(n))
# Another simplification:
# - it should return an integer x such that x * x <= n
#   and (x + 1) * (x + 1) > n
#   ^^^ this is the one we will use.

# 3. Translate the spec to Hypothesis and check
# This step will depend on the tool.
# As a Hypothesis test: - @given annotation and a unit test.
# @pytest.mark.skip # comment out to run
@given(st.integers(min_value=0, max_value=10_000))
def test_integer_sqrt(n):
    ans = integer_sqrt(n)
    # one line or two lines?
    assert (ans * ans) <= n
    assert (ans + 1) * (ans + 1) > n

# Some examples to try running the program
# print(integer_sqrt(3))
# print(integer_sqrt(4))
# print(integer_sqrt(6))
# print(integer_sqrt(-3))

"""
=== Checking our understanding ===

True/False
- The function integer_sqrt satisfies the specification we wrote in test_integer_sqrt.

Which of the following additional specifications does integer_sqrt satisfy?
1. The output of integer_sqrt is always an integer.
2. If the input to integer_sqrt is an integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

https://forms.gle/7cYDGoNfLmtXD5Fa9

Answers:

True
1, 2, 3, 5, and 7

True - "true" is the spec satisfied by all programs!

True == any program is valid

False == no program is valid

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

(Let's run the code)
"""

"""
.
.
.
.
.
(if it works)

spec works!
Program satisfies the spec!

We are happy! --> we think we've implemented the program correctly
    (AND, we've specified it correctly)

=== Q+A ===

Q: How valuable is this spec?
   Have we tested EVERYTHING about the program?

A: No, for example, we didn't test it on negative inputs.

  For now: no spec is perfect! Writing and defining precise & helpful specs
  is an art and it's something that we will continue to get more practice with.

Q: are properties about the syntax or lines of code considered specifications?
    E.g.: the function must have at least 10 Lines of code

A: Yes, that's a valid spec but probably not one we're interested in.

=== Segue ===

The above exercise is a good segue into two topics we want to cover next
(over the next two lecture parts):

1. Stronger and weaker specifications

2. Types of specifications / ways of writing specifications.

=== Stronger and Weaker Specifications ===

Definition.

Let S1 and S2 be specifications

- S1 is *stronger* than S2
    if every program satisfying S1 satisfies S2.

    i.e.

        if the set of programs satisfying S1 is a subset (or equal) to the set of programs satisfying S2

    Think of an example:
    "S1 = the output is 1"
    "S2 = the output is odd"

    which is stronger?

        S1 is stronger because
        any program where the output is equal to exactly 1,
        also satisfies "the output is odd"

    the set of programs outputting 1 is a subset of the set of programs whose output is odd.
    S1 is constraining the program more (giving more information about the program,
    so S1 is stronger).

    S1 is more restrictive, more specific, or more particular than S2.

    btw:
        S1 is stronger than S1
        S2 is stronger than S2.

- S1 is *weaker* than S2
    means the same thing as S2 is stronger than S1.

    i.e.:

        if the set of programs satisfying S2 is a subset of the set of programs satisfying S1.

Special cases:

    False (the specification true of no programs)
        = the empty set of programs, which makes it the strongest possible spec

    If you give me any spec (your definition of correctness) S

        False is stronger than S

    True (the specification true of all programs)
        = the set of all programs, which makes it the weakest possible spec.

    If you give me any spec (your definition of correctness S),

        True is weaker than S.

Think of it this way: if I write a unit test or Hypothesis test, and I put

    assert True

that's equivalent to saying nothing. (will pass for all programs) If I put

    assert false

that will always fail! that fails for all programs.

And all of our other examples so far (e.g., the spec is_even, test_integer_srt, etc.
are somewhere in between the two extremes.)

=== Exercise ===

Let's sort the above specifications by which is stronger/weaker than the others.

Let's do this exercise together as a class --
if we don't finish it, we will do it as next time's poll.

1. If the input to integer_sqrt is a nonnegative integer, then the output is an integer.
2. If the input to integer_sqrt is a positive integer, then the output is an integer.
3. True (true of all programs)
4. False (false of all programs)
5. The input arguments are not modified by the program.
6. If the input is greater than 100, then the output is greater than 10.
7. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

Let's try to sort all of these by which are stronger and weaker.

To start:
    4 is the strongest
    3 is the weakest

7 is stronger than 6?
    ==> not quite -- neither 6 nor 7 is stronger than the other

1 is stronger than 2?

    Strongest
       4
     /   \     \   \
    1     |    |    |
    |     6    7    5
    2     |    |    |
     \   /    /    /
       3
    Weakest

"""

"""
Additional Exercise:

- For specifications 6 and 7, write an example program
  which satisfies one spec and not the other.

Some of us thought that 6 was stronger than 7!

Let's disprove that and find an example that satisfies 6 but not 7.

(The homework has some similar exercises!)
"""

# 6. For all integer inputs x, If the input is greater than 100, then the output is greater than 10.
# 7. For all integer inputs x, If the input is greater than or equal to 100, then the output is greater than or equal to 10.

# Between 6 and 7, is either one stronger?

def prog_ex(x):
    if x > 100:
        return 11
    elif x == 100:
        return 9
    else:
        return None

@given(st.integers(min_value=-10_000, max_value=10_000))
@settings(max_examples=10_000)
def test_prog_ex_spec_6(x):
    if x > 100:
        # run our program
        y = prog_ex(x)
        # assert the output is > 10
        assert y > 10

@given(st.integers(min_value=-10_000, max_value=10_000))
@settings(max_examples=10_000)
@pytest.mark.xfail
def test_prog_ex_spec_7(x):
    if x >= 100:
        # run our program
        y = prog_ex(x)
        # assert the output is >= 10
        assert y >= 10

"""
The program we wrote should satisfy spec 6 but not spec 7.

This can be confusing!

    Even though spec 7 tests a *wider range* of inputs --
    in other words, has a *weaker* requirement on the input --
    spec 7 is not weaker than spec 6.
    in this case, neither spec 6 nor spec 7 is stronger than the other.

Exercise:

    Also write a program that satisfies spec 7 but not spec 6.

Let's try one other thing,
remember I restricted the input above (using @given) somewhat arbtrarily
to between 100 and 120.
What happens if I don't do this?

Let's try running with

@given(st.integers(min_value=-10_000, max_value=10_000))

=== Problem? ===

This reveals a problem with Hypothesis!
Hypothesis tries random inputs, but in this case, it failed to try
the input 100, so it failed to find the input which falsifies specification 7.

This is sometimes called a "flaky test" -- it's a test that sometimes passes
or fails randomly depending on the program execution.

One way to fix is (as we do above) by reducing the range of inputs we consider
(perhaps not very satisfying)

Another way to fix is by increasing the number of inputs we try (better - the
homework shows how to do this, @settings(...))

    @settings(max_examples=10_000)

    (default is 100)

This fixes it in this case - but might not catch all other edge cases
(e.g., generating x=100,000 from x between -10M and 10M)
if those edge cases are just vanishingly small compared to passing inputs.

This is a fundamental limitation of testing specifications,
and is why we will turn to verifying them (i.e., actually proving
whether the spec holds or not) in the coming lectures.
This is what we will do in Z3 in Dafny.

Recap:

- We talked about stronger/weakers specs
- We did some exercises practicing the methodology of working with Hypothesis,
  similar to what you will do on the HW
- We did an example of coming up with a specific program satisfying spec S1 but
  not S2, and saw limitations of Hypothesis.
"""
