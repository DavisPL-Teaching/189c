"""
Lecture 1
ECS 189C
April 3, 2024
"""

######################
###     Part 1     ###
######################
# Components of correctness: programs, specifications, and preconditions

from hypothesis import given
from hypothesis import strategies as st

def average(l):
    return sum(l) / len(l)

# *** Has all three main components!!! ***
# @given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))
# def test_average(xs):
#     assert min(xs) <= average(xs) <= max(xs)

# Note the argument xs -- this is called random testing!
# Usually contrasted with unit testing.

# Common experience unit testing:
def ignore_test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0

# ignore_test_average_function()

# This is really tedious!
# Hypothesis makes it easier by generating all of these tests (and more)
# automatically.

# It's also unclear if my tests are really thorough.
# I haven't included:
# - any lists with negative numbers
# - any lists with both floats and integers
# - any lists with repeated elements

######## Components ########
"""
**Key idea**
The hypothesis example has all three components of correctness
that we want to talk about.

1. A program: This is the average function.
def average

2. A specification: This is the property that the average of a list
  is between the minimum and maximum elements of the list.
assert min(xs) <= average(xs) <= max(xs)

3. A precondition: This asserts what properties we are *assuming* that our input will have when the funciton is called.
@given(st.lists(st.floats(allow_nan=False, allow_infinity=False), min_size=1))

Natural language vs. formal specifications
For example:
"This is the property that the average of a list
  is between the minimum and maximum elements of the list."
is a natural language specification
"assert min(xs) <= average(xs) <= max(xs)"
is the formal specification.
Generally you should go from starting with a natural language
spec to going to a formal spec.
Think about what your program SHOULD do, explain it in words,
and then write it down programmatically.

Definition of correctness

Slightly more formally:

1. What is a program? For our purposes, a program is something
that you can run and stuff will happen.
It has:
- An input (some keys/words/etc. the user types)
- An output (something that happens or gets returned at the end)
May also have:
- Various other behaviors as the function is executed (e.g.,
prints stuff to stdout, opens up Google.com on your browser,
deletes your home directory, reads from id_rsa and sends it
to an unknown email address, etc.)
To summarize the output and behaviors part:
Basically, a sequence of events/behaviors happen when its executed.
^^ i.e. a program execution

2. What is a specification (or spec, for short)
WORKING DEFINITION: let's say that a
spec is a logical constraint on the behaviors that should occur
when the program is executed.
Well I mean:
a) Some sequences of behaviors are OK
b) Some sequences of behaviors are not OK.
In other words, it's a boolean property on program executions.

3. What is a precondition?
A boolean property on program inputs.
Some inputs are OK, some are not.

The difference between (2) and (3) is:
- (2) is a requirement/assertion.
- (3) is an assumption.

def divide(x, y):
    x / y

Notice I haven't asserted that y != 0
Therefore y != 0 is a precondition of this program.

Another example, in lots of C code you'll see things like

void buffer_write(x: *char, idx: i32, val: char):
    x[idx] = char

This is an important example of preconditions because if idx
is outside of the bounds of the array, there's really nothing
that the program can guarantee

A program is **correct** if
for all inputs x satisfying the preconditions,
and if I execute the program on x,
the program execution satisfies the spec.
"""

# Another example

def list_product(l):
    result = 1
    for x in l:
        result *= x
    return result

# (Of course we could just use built-in from functools
# or implement this with reduce or whatever.)

from functools import reduce

@given(st.lists(st.integers()))
def test_list_product(xs):
    # Unit examples
    # assert list_product([]) == 1
    # Not very interesting!
    # More interesting: check that our implementation
    # matches the standard/expected implementation.
    assert list_product(xs) == reduce(lambda x, y: x * y, xs, 1)

############## where we left off for day 1 ############

######################
###     Part 2     ###
######################

# Announcements

# git clone https://github.com/DavisPL-Teaching/189C.git
# 60, waitlist 12

# Last time

# - Defined what it means for programs to be correct
# - Defined specifications
# - Example specifiacations
# - Started to get used to Python + Hypothesis syntax

# Review: writing specifications
# list product example:
# Spec:
# - we test whether our impl matches the intended behavior.

# average of a list example:
# Spec:
# - we test whether our impl satisfies a property of interest.

# Plan for today
# - Short review
# - Quiz
# - Practice writing more complex specifications
# - Talk about different types of specifications
# - Talk about preconditions
# - Do a programming exercise

# One more example:
def double_list(l):
    # Program or implementation
    result = []
    for x in l:
        result.append(2 * x)
    return result

# Specification
@given(st.lists(st.integers()))
def test_double_list(l):
    new_list = double_list(l)
    # range(5) = numbers between 0 and 4
    for i in range(len(l)):
        assert new_list[i] == 2 * l[i]

# Review: correctness requires:
# - Model of the program (in our case, a Python program)
# - Model of what should happen (in Hypothesis, we do this through assertions)
# - Model of the input (precondition) (in Hypothesis, we do this through @given decorators which are run using pytest)

"""
Comments

"All models are wrong, some are useful."
- attributed to George E. P. Box

"The best model of a cat is a cat, especially the same cat."
- Unknown
"""

########## Poll ##########

from math import sqrt

def square_root(x):
    return int(sqrt(x))

# POLL: Come up with a specification for the program.
# Also, come up with a specification that does NOT hold of the program.
# You can write either as a Python function or in words.

# https://tinyurl.com/57upuhcw

# Examples
# >>> int(sqrt(4))
# 2
# >>> int(sqrt(5))
# 2
# >>> int(sqrt(10))
# 3

@given(st.integers(min_value = 0, max_value = 1000000))
def test_square_root(x):
    # what should go here?
    # Try to make it more interesting that just a specific example
    # Ex.: Square_root(x) is a function where it returns a number, when multiplied by itself, equals x.
    y = square_root(x)
    assert y * y <= x and (y + 1) * (y + 1) > x

########## Hypothesis syntax ##########
# https://hypothesis.readthedocs.io/en/latest/data.html

# Some additional useful features

# - Other @given strategies

# - the @example syntax

from hypothesis import example

@given(st.integers(min_value = 0, max_value = 100))
@example(x=10000)
def test_square_root_2(x):
    y = square_root(x)
    assert y * y <= x and (y + 1) * (y + 1) > x

# Writing specifications: additional notes

# Important note: the same function can have multiple specifications!
# Examples:

def list_interleave(l1, l2):
    # Return a list with the elements of l1 and l2 interleaved
    result = []
    n = min(len(l1), len(l2))
    for i in range(n):
        result.append(l1[i])
        result.append(l2[i])
    return result

# ex.: interleave([1, 4, 5], [2, 3, 6] --> [1, 2, 4, 3, 5, 6])

@given(st.lists(st.integers()),st.lists(st.integers()))
def test_list_interleave(l1, l2):
    l = list_interleave(l1, l2)
    # Weak spec
    assert len(l) == min(2 * len(l1), 2 * len(l2))
    # Stronger spec: check that the elements are as we expect
    # for i in range(..):
    # check that l[2 * i] = l1[i]
    # check that l[2 * i + 1] = l2[i]

# Skip
def ncr(n, k):
    # Return the number of ways to choose k items from n items
    result = 1
    for i in range(k):
        result *= n - i
        result //= i + 1
    return result

# What can we check about this function?

# A more interesting one:

def functional_map(f, l):
    return [f(x) for x in l]

# how to generate f?
# Let's check the documentation
@given(st.functions(like=lambda x: x,returns=st.integers()),st.lists(st.integers()))
def test_functional_map(f, l):
    result = functional_map(f, l)
    assert len(result) == len(l)

# Review:
# - We talked more about writing specs
# - The same function can have multiple specs, and it can have
#   incorrect speccs
# - The process of writing a spec can be a good tool for debugging
#   BOTH problems with the function, and problems with the spec.

############## where we left off for day 2 ############

# Also, a *different* function can satisfy the same specification

def list_product_2(l):
    # TODO
    pass

# When a specification is wrong...

def repeated_square(x, n):
    # TODO: implement
    pass

# Fixing the average function

# def test_average_2(l1, l2):
#     assert average(l1 + l2) == (average(l1) + average(l2)) / 2

# def test_average_3(l1, l2):
#     avg1 = average(l1)
#     avg2 = average(l2)
#     assert min(avg1, avg2) <= average(l1 + l2) <= max(avg1, avg2)

# def test_average_4(l1, l2):
#     assert average(l1 + l2) == (len(l1) * average(l1) + len(l2) * average(l2)) / (len(l1) + len(l2))

######################
###     Part 3     ###
######################
# Types of specifications

def repeated_square_2(x, n):
    # TODO: implement
    pass

# - Basic properties or patterns
# - Functional correctness specifications
# - Loop invariant specifications
# - Type specifications

# A **safety property** is...
# Everything we have seen so far is a safety property.

######################
###     Part 4     ###
######################
# Writing preconditions

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

######################
###     Part 5     ###
######################
# Live coding project: War implementation

######################
###     Part 6     ###
######################
# Limitations and discussion

#     - Specification is wrong

#     - Specification is incomplete

#     - Program model is wrong

#     - Precondition is wrong

#     - Mutability issues

#     - Techniques for validating specifications

#     - Important distinctions (terminology to be aware of)
#         + Testing vs. verification
#         + Static/dynamic
#         + Soundness/completeness
#         + White-box vs. black-box
