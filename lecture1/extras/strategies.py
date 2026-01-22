#############################
###     Optional Part     ###
#############################
# More about strategies

"""
NOT part of the spec:
- the program
- the strategy (generator)

We've seen some strategies already:
- st.integers()
- st.lists() -- given as a parameter a base strategy
    for generating elements of theh list.

What is the difference between a strategy and a precondition?
    st.lists(st.integers(), min_length = 1)
The strategy is an st.lists object, the precondition is just
the statement "l is a list of integers of length at least 1."

Example strategies:
(written as Python generators)
"""

def gen_simple():
    # generate sequential inputs
    for i in range(0, 1000):
        yield i

from random import randint

def gen_smarter():
    # generate completely random inputs
    # import a random number generator
    while True:
        yield randint(-10000, 10000)
    # Also not perfect and you can do better.

def gen_simpler():
    while True:
        yield 7
    # Probably not a good strategy
    # https://imgur.com/uR4WuQ0

"""
Some other useful strategies:
- st.text() -- for generating (valid) strings
- st.one_of() -- generates one thing or the other
    st.one_of(st.integers(), st.floats())
- st.functions() -- generates functions with a given signature

Hypothesis generators are much smarter than just generating
random values.

Minimizing examples:
    https://hypothesis.readthedocs.io/en/latest/data.html
    Once Hypothesis finds a failing example, it doesn't give up,
    it will continue searching to find a "minimal" example
    to show to the user

Custom formats: (emails, dates, etc.)
    st.text() -- UTF8 by default
    st.datetimes()
    st.emails()
    (you can also write your own)

Guiding the search:
    assumptions: https://hypothesis.readthedocs.io/en/latest/details.html#making-assumptions
    target: https://hypothesis.readthedocs.io/en/latest/details.html#hypothesis.target
"""

@given(st.floats(0, 1e100), st.floats(0, 1e100), st.floats(0, 1e100))
@pytest.mark.skip
def test_associativity_with_target(a, b, c):
    ab_c = (a + b) + c
    a_bc = a + (b + c)
    difference = abs(ab_c - a_bc)
    target(difference)  # Without this, the test almost always passes
    assert difference < 2.0

"""
Summary:
How hypothesis works, roughly:

1. Generate a random example

2. Run the example

    a. If it encounters a precondition/assume:
        does it satisfy the precondition?
        - If YES, continue
        - If NO, move on to the next test
            + on the next run, try to guide the search towards a passing example

    b. If it encounters an assertion:
        does it satisfy the assertion?
        - If YES, continue
            + on the next run, try to guide the search towards a failing example
        - If NO, report a failure -- go to step 4

4. Once a failing assertion is found:
    try to simplify the example ("shrink") it to something understandable.
"""
