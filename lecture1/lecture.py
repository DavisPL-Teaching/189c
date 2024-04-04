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
def test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0

test_average_function()

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

    # assert list_product(xs) == (xs)

############## where we left off for today ############

# A third example
def apply_to_each(f, l):
    return [f(x) for x in l]

def test_apply_to_each():
    # TODO
    pass

"""
Comments

"All models are wrong, some are useful."
- attributed to George E. P. Box

"The best model of a cat is a cat, especially the same cat."
- Unknown
"""

######################
###     Part 2     ###
######################

# Hypothesis syntax
# https://hypothesis.readthedocs.io/en/latest/data.html

# Writing specifications

def list_append(l1, l2):
    return l1 + l2

def list_interleave(l1, l2):
    # Return a list with the elements of l1 and l2 interleaved
    result = []
    for i in range(len(l1)):
        result.append(l1[i])
        result.append(l2[i])
    return result

def ncr(n, k):
    # Return the number of ways to choose k items from n items
    result = 1
    for i in range(k):
        result *= n - i
        result //= i + 1
    return result

# What can we check about this function?


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

########## Poll ##########

def do_twice(f, x):
    return f(f(x))

def test_do_twice():
    # TODO: here
    pass

# POLL: Come up with a specification for the program.
# (You can assume x is an integer and pick any function f.)
#
# Is your specification correct?
# What are some limitations of this specification?

# https://tinyurl.com/57upuhcw

######################
###     Part 3     ###
######################
# Types of specifications

# Sorting example




######################
###     Part 4     ###
######################
# Writing preconditions

# Divide by zero example


# - Average example


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
