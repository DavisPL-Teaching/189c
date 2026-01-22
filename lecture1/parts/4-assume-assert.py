"""
Lecture 1, Part 4:
Assume and Assert

Question:
What are all possible specifications that can be expressed through
tests?

    ... through Hypothesis tests?

===== Assume and assert =====

Going back to our divide by zero example.

What if we want to write it to include positive and negative integers,
not only positive integers?
"""

# Imports
import pytest
from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

from hypothesis import assume

def divides_2(x, y):
    return x / y

ERROR = 0.00001

@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = -1000, max_value = 1000),
)
@settings(max_examples=1000)
def test_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y != 0) # If this isn't true, throw away this particular test run.
    # assert type(divide(x, y)) is float
    assert abs(divides_2(x, y) * y - x) < ERROR

"""
These two little functions, assume and assert, turn out to be
fundamentally important to testing & verification.

- Assert: This property should hold, if it doesn't, that's an
    error. I want to report a test failure.
- Assume: This property should hold, if it doesn't, I want to
    ignore this test.

Another way to think about them (if you are more systems-oriented):
if we imagine a program that is just a single standalone unit test,
it's sort of like
"""

import sys

def my_assert(b):
    if not b:
        # halt the program with an error, test failed :-(
        sys.exit(1)
        # in Pytest/Hypothesis, what happens:
        # raise AssertionError("assertion failed")

def my_assume(b):
    if not b:
        # halt the program -- no error, test passed :-)
        sys.exit(0)
        # in Pytest/Hypothesis, what happens:
        # ignore this run, move on to the next test case.

"""
Assert and assume interact in interesting ways...

Poll:

Which of the following has no effect? (Select all that apply)
- assert True
- assert False
- assume True
- assume False
- assert P if it occurs immediately following assume P
- assume P if it occurs immediately following assert P

Poll link:
https://forms.gle/8jKUbC6fQv4hDNmA6

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

Some of you may have picked up on the facts that:

- preconditions are just assume() statements
- postconditions are just assert() statements.

Asuming f is a function like

    def f(x):
        // ... do something
        return y

precond P, program f, postcondition Q
    == equivalent to ==
    assume(P(x))
    y = f(x)
    assert(Q(y))

We have to be careful with assume!
It's very dangerous.
"""

# Another example
# Is this program for sorting a list correct, according to the spec? :)

def sort_list(l):
    l = l.copy()
    return l

# The spec:
@given(st.lists(st.integers()))
def test_sort_list(l):
    assume(l == sorted(l))
    assert sort_list(l) == sorted(l)

"""
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

Multiverse view
- Quantum bogosort:
    https://wiki.c2.com/?QuantumBogoSort
- (Based on: bogosort
    https://en.wikipedia.org/wiki/Bogosort)

Q: In what cases is assume better than using if?
A: They're not really that different.

    assume(P)

    is really the same as:

    if P:
        <continue rest of test, put all assertions here>
    else:
        pass, exit normally

    What's dangerous? Putting all of your test logic in a specific branch,
    where only some conditions are true, and failing to test for other edge cases.

    General lesson: don't exclude edge cases from consideration.

Another way of thinking about this is, whose responsibility is
it to ensure the list is sorted?
- If I use assume, I'm saying it's the caller's responsibility.
- If I use assert, in a specification to say that some property
  is true, then I'm saying it's the function's responsibility
  to guarantee that property.
"""

"""
Punchline:

Hypothesis can express exactly those specifications that are
expressible using assume() and assert().

Precise statement:

- On all input executions such that all assume() statements
  hold up to a given point,
  all assert() statements hold after that point.

- @given is functionally equivalent to an assume statement,
  though it is implemented differently, using something called
  "strategies"

    import hypothesis.strategies as st
    https://hypothesis.readthedocs.io/en/latest/reference/strategies.html

    More about strategies: see
        extras/strategies.py

- assume and assert can be used to write general program specifications and will reoccur in many of the tools covered in this class.

- assume is dangerous! Be careful about using it or you end up excluding cases that are actually
  important.
"""
