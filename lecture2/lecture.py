"""
Lecture 2

git clone https://github.com/DavisPL-Teaching/189C.git
or
git pull
(If you have changes, you will want to discard them first.)
"""

####################
###     Poll     ###
####################

# Here are 3 programs, and 3 specifications. For each program, which
# specification(s) does it satisfy?
# For all programs, assume that the input is an arbitrary integer.

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

# Divide by zero example
def divide(x, y):
    # TODO
    pass

# - Average example from before
def average(l):
    pass

# You can often read off preconditions from the documentation!
# Examples:
# - list pop: https://docs.python.org/3/tutorial/datastructures.html
# - file open: https://docs.python.org/3/library/functions.html#open

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
