"""
Lecture 1, Part 2:
Stronger and weaker specifications

=== Intro ===

Recap: we know about
    - spec: a true or false property of a program
    - Python assertions are specifications!
    - Hypothesis: a tool for writing and testing specifications
    - testing vs. verification

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
"""

# We might need this
from math import sqrt

# 1. Write the program
def integer_sqrt(n):
    # TODO: implement
    raise NotImplementedError

# 2. Write the specification - first in English
# TODO
# ...
# ...
# ...

# 3. Translate the spec to Hypothesis and check
# This step will depend on the tool.
# As a Hypothesis test: - @given annotation and a unit test.
@pytest.mark.skip # comment out to run
# @given(st.integers(min_value=0, max_value=10_000))
def test_integer_sqrt(n):
    ans = integer_sqrt(n)
    # assert ...

# Some examples to try running the program
# print(integer_sqrt(3))
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

=== Question ===

Q: are properties about the syntax or lines of code considered specifications?
    E.g.: the function must have at least 10 Lines of code
    A: Yes, that's a valid spec but probably not one we're interested in.

=== Segue ===

The above exercise is a good segue into two topics we want to cover next:

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
    the set of programs outputting 1 is a subset of the set of programs whose output is odd.
    S1 is constraining the program more (giving more information about the program,
    so S1 is stronger).

- S1 is *weaker* than S2
    means the same thing as S2 is stronger than S1.

    i.e.:

        if the set of programs satisfying S2 is a subset of the set of programs satisfying S1.

Special cases:

    False (the specification true of no programs)
        = the empty set of programs, which makes it the strongest possible spec

    True (the specification true of all programs)
        = the set of all programs, which makes it the weakest possible spec.

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
"""

"""
Additional Exercise:

- For specifications 6 and 7, write an example program
  which satisfies one spec and not the other.

(The homework has some similar exercises!)
"""

# 6. For all integer inputs x, If the input is greater than 100, then the output is greater than 10.
# 7. For all integer inputs x, If the input is greater than or equal to 100, then the output is greater than or equal to 10.

# Between 6 and 7, is either one stronger?

def prog_ex(x):
    # TODO
    raise NotImplementedError

@given(st.integers(min_value=0, max_value=10_000))
@pytest.mark.skip
def test_prog_ex_spec_6(x):
    # TODO
    raise NotImplementedError

@given(st.integers(min_value=50, max_value=200)) # <- precondition
@pytest.mark.skip
def test_prog_ex_spec_7(x):
    # TODO
    raise NotImplementedError

"""
The program we wrote should satisfy spec 6 but not spec 7.

=== Problem? ===

This reveals a problem with Hypothesis!
Hypothesis tries random inputs, but in this case, it failed to try
the input 100, so it failed to find the input which falsifies specification 7.

One way to fix is (as we do above) by reducing the range of inputs we consider
(perhaps not very satisfying)

Another way to fix is by increasing the number of inputs we try (better - the
homework shows how to do this, @settings(...))

    @settings(max_examples=10_000)

    (default is 100)

But, this is a fundamental limitation of testing specifications,
and is why we will turn to verifying them (i.e., actually proving
whether the spec holds or not) in the coming lectures.
This is what we will do in Z3 in Dafny.
"""
