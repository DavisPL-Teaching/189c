"""
Lecture 2

git clone https://github.com/DavisPL-Teaching/189C.git
or
git pull
(If you have changes, you will want to discard them first.)
"""

from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings
from hypothesis import assume
import pytest

####################
###     Poll     ###
####################

# Here are 3 programs, and 4 specifications. For each program, which
# specification(s) does it satisfy?
# For all programs, assume that the input is an arbitrary integer.

# The decorator is generating an arbitrary integer
# @given(st.integers())

# Programs:
def p1(x):
    return x + 1
def p2(x):
    return x + x
def p3(x):
    return x * x + 1

# Specifications:
def s1(x):
    assert type(p(x)) is int
def s2(x):
    assert p(x) > x
def s3(x):
    assert p(x) == x * x
def s4(x):
    assert p(1) == 2

# FORM: https://tinyurl.com/2p79r6y6

######################
###     Part 1     ###
######################
# Writing preconditions
# + useful Hypothesis/pytest syntax

# We've seen preconditions already: we've seen the
# @given(...)
# decorator, which tells us what input strategy to use.
# We can further refine the precondition by putting in constraints like
# for example:
# @given(st.integers(min_value = 0, max_value = 1000000))

# Here, the precondition (in words) is that
# "The input is an integer between 0 and 1,000,000, inclusive."

# Divide by zero example
# input two integers
def divide(x, y):
    return x / y

@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = 1, max_value = 1000),
)
@settings(max_examples=10000)
@pytest.mark.xfail
def test_divide(x, y):
    # what to test here?
    z = divide(x, y)
    # Spec ideas:
    # z is less than the difference between x and y
    assert z < abs(x - y)
    # ^^ seems to be true -- but fails for a rare input set,
    # e.g. x = 2, y = 1

# We couldn't even test our statement, because our program
# crashed :(
# Exception handling?
# this is exactly what preconditions are for.
# Let's directly make sure the thing we are dividing by (y)
# is > 0.

# Q: How do we exclude only zero?
# A: Use an assume statement
@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = -1000, max_value = 1000),
)
@settings(max_examples=10000)
def test_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y != 0)
    assert type(divide(x, y)) is float

# Another bit of useful syntax:
# As we've seen, Hypothesis tests are run through pytest,
# which is Python's unit testing framework. We can use
# @pytest.mark.skip(reason = "Reason")
# @pytest.mark.xfail
# To mark a test as either ignored, or expected to fail.

# SKIP
# - Average example from before
def average(l):
    pass

"""
You can often read off preconditions from the documentation!
Examples:
- list pop: https://docs.python.org/3/tutorial/datastructures.html

    "It raises an IndexError if the list is empty or the index is outside the list range."

    This is another way of saying that the precondition of
    list.pop() is that the list should be nonempty.

- file open: https://docs.python.org/3/library/functions.html#open

    Has a number of preconditions:
    - The file should be able to be opened (OSError otherwise)

    - "If closefd is False and a file descriptor rather than a filename was given, the underlying file descriptor will be kept open when the file is closed. If a filename is given closefd must be True (the default); otherwise, an error will be raised."

Point: exceptions are often used to enforce preconditions --
if we don't know what to do on a particular input, we crash the program

Note that we can model exceptions in our specification in two
ways:
- If the exception is expected behavior, we can test that
  when the function is run on the bad input, the exception is raised.
  This does NOT involve excluding the input via the precondition,
  instead we write an assertion to expect the correct behavior.

- If the exception is not expected behavior, or if we don't
  want to consider inputs for which the exception is raised
  as valid, we can exclude them via a precondition.
"""

# Recap:
# We looked at writing preconditions
# We learned two useful ways of writing preconditions:
# - @given syntax with explicit parameters
# - assume(...) syntax

# - Mentioned some other useful pytest/Hypothesis syntax.

############## where we left off for day 3 ############


# Also, some useful syntax.

# Strategies:
# - st.text()
# - st.one_of()

# Decorators:
# @pytest.mark.skip(reason="...")
# @pytest.mark.xfail
# @example(...)

# Advanced:
# the assume() statement

######################
###     Part 2     ###
######################
# Weaker and stronger specifications

"""
As we have seen, there are many different specifications
that can be written for a function.
We can speak about these being weaker or stronger than each other...

- Weaker: Less specific, more programs satisfy it
- Stronger: More specific, fewer programs satisfy it

The weakest possible specification is one that is always true, regardless of the
function:

    def test_weakest_spec():
        assert True

Of course, this is rather pointless, but it is a specification!

Similarly, the strongest possible specification is one that is always false:

    def test_strongest_spec():
        assert False

This is also not very useful, as it is not true of any function.
But again, it is a specification!

Example:
"""

def count_unique(l):
    """
    Given a list l, returns the number of unique elements in l.
    """
    unique = 0
    l = l.copy()
    while l != []:
        x = l.pop()
        if x not in l:
            unique += 1
    return unique

"""
Some properties

(each one should be stronger than the last!)

The output is always an integer.

Trivia:

The output is between 0 and the length of the input list, inclusive.

The output is equal to a standard implementation of the same function.
"""

"""
Stronger properties??

The output of the function is equal to len(set(l)),
AND if the function is called again with the same input list,
it returns the same output again.
"""

"""
Types of specifications:

- Functional correctness:
    ...
- Safety properties:
    ...

Everything we have seen so far is just about functional correctness.
Also, we have only seen safety properties.
"""

######################
###     Part 3     ###
######################
# Weaker and stronger preconditions
# (if time)

def take_elems(l, n):
    """
    Given a list l and an integer n, returns the first n elements of l.
    If n is greater than the length of l, returns l.
    If n is negative, raises an error.
    """
    if n < 0:
        raise ValueError("n must be nonnegative")
    return l[:n]

######################
###     Part 4     ###
######################
# Discussion and limitations

"""
The technical name for Hypothesis is that it's a "property-based testing tool" (PBT). Why?

### Advantages

Some more about advantages:
https://news.ycombinator.com/item?id=34450736

"I've never introduced property tests without finding a bug in either the specification or implementation. I have repeatedly spent time figuring out where the bug was in my property testing library before realising that it was correct and the obviously correct code I was testing was actually wrong."

### Disadvantages

Most important limitations,
these are not specific to Hypothesis (!)

- Specification could be wrong

- Specification could be incomplete

- Program model could be wrong

- Precondition could be wrong

You will see some other limitations on HW1 (part 2).

As a testing tool, Hypothesis has its own specific limitations.
For example?

"Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence." - Edsger Dijkstra
"""
