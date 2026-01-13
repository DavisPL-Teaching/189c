"""
Lecture 1: Program Specifications
ECS 189C

Part 1: Writing Specifications

=== Program specifications ===

A specification is any true or false property about a program.

- By "program", at this stage, just think of this as any function in Python.

Any given program
- "satisfies" the specification if the property is true for that program
- "does not satisfy" the specification, i.e. the property is false

Some programs satisfy the property (spec), others don't.
Like an answer key for a test question.

Recall the is_even function from Lecture 0:
"""

def is_even(x):
    if x == 1:
        return False
    elif x == 2:
        return True
    elif x == 3:
        return False
    elif x == 4:
        return True
    else:
        return False

# example
# spec: whenever other_prog calls is_even, the argument is between 0 and 4
# def other_prog():
#     x = 7
#     is_even(7)

"""
=== Discussion Question and Poll ===

Which of the following is NOT a specification for the is_even function, according to the above definition?
Select all that apply.

https://forms.gle/A1F35xpv73Pw3jhy8

Recap:

A specification is a true or false property of a program.

    --> I give you a program, you decide if it's correct or not
        (yes or no answer).
"""

# Specifications in natural language
# SPECIFICATION:
# On all inputs x, is_even(x) should return whether or not x is even.
# On inputs x that are ...,
def is_even_2(x):
    """
    (Docstring)

    @x: x is an integer
    Returns: true if x is even, false otherwise.

    ^^ This docstring is a specification!

    That's the same as:
    "On all inputs x such that x is an integer, is_even(x) returns true
     iff x is even."

    It's written in English, not in a formal langauge that we can
    apply automated tools to.
    """
    # <Body omitted>
    pass

"""
Problem:
You've written your program and your docstring,
but later on, the program gets edited!

Developer forgets to update the docstring

Docstring is now out of date! But nothing failed - the program still runs,
we didn't realize that anything went wrong.

So: second step is to write unit tests.

Unit tests are an example of specifications!

Example:
"""

import pytest

# Unit test
# Comment out to run
@pytest.mark.xfail
def test_is_even():
    # This is a specification!!
    assert is_even(4)
    assert not is_even(3)
    # This is also a specification!
    # Fails because is_even(6) returns False
    assert is_even(6)

# run: pytest 1-specifications.py

"""
The unit test corresponds to a specification:

    "is_even(4) return true; is_even(3) should return false; and is_even(6) should return true)."

You may not know it, but you write specifications every day while programming!
Every time you write an "assert" statement or a unit test, you are writing a specification.

Unit testing is helpful!
Unit testing can be considered a form of writing specifications.
(Why?)

In this class, we're generally interested in writing specifications that can be automatically
tested - or at least validated, whether or not the specification is true for that program.

We call these "formal specifications" - often written in mathematical or logical syntax.

=== Writing specifications ===

We will use Hypothesis for the first part of the course.

We can use Hypothesis tog et practice writing specifications,
before diving into the later parts of the course.

Hypothesis uses a technique called *random testing* to try to identify
whether specs are true or false.

=== Hypothesis ===

To install:

    - Check your python version: python3 --version
    - Check your pytest version: pytest --version
    - Install Hypothesis:

        pip3 install hypothesis

    (Note: I know this is not the right way to actually install Python packages,
    but I'm lazy)
"""

# Starting with imports...
from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

# We don't need this yet, but will need it later
import pytest

"""
To run:

    pytest lecture1.py

"""

# First, we need a program to test
def average(l):
    return sum(l) / len(l)

# Next, we need to write down a specification

# Using Hypothesis to test specifications
# This causes Hypothesis to automatically generate a unit test
# The unit test will: run a bunch of random inputs, try running the program,
# and raise an error if any assertions are violated.
@given(st.lists(st.floats(allow_nan=False, min_value=0, max_value=100, allow_infinity=False), min_size=1))
# @pytest.mark.skip
# @settings(verbosity=3)
def test_average(xs):
    # Fixed version from lecture
    EPSILON = .00000001
    assert min(xs) - EPSILON <= average(xs) <= max(xs) + EPSILON

"""
Lessons learned:
- Floating point is difficult
- Always compare floating points within an error of some EPSILON constant
- Writing specs can help challenge our assumptions

=== More about random testing ===

What is random testing?

--> We are given a program, and a spec about that program
    (The spec is written as a test, in this case using pytest)
--> We run the program on a bunch of random inputs, and try to check
    if the spec is true or not.

Note the argument xs -- this is called random testing!
Usually contrasted with unit testing.

Q1:
- Is Pytest a part of Hypothesis?

    Pytest is the most common Python unit test framework

    pytest <prog.py> <-- how you run the tests on your program
    It will run anything that starts with test_

    Hypothesis is a random testing tool that integrates with pytest.

- How can we be sure that we're actually testing every input?

    We can't! :-)

    Good foreshadowing to the tools we'll cover later -
    this is the difference between "testing" and "verification".

Some additional motivation:
Here's a common experience when doing unit testing:
"""

# Common experience unit testing:
@pytest.mark.skip
def test_average_function():
    assert average([1, 2, 3]) == 2
    assert average([1, 2, 3, 4]) == 2.5
    assert average([1, 2, 3, 4, 5]) == 3
    assert average([2.0]) == 2.0
    # ^^ long list of cases that may or may not be exhaustive!

# ignore_test_average_function()

"""
This is really tedious!
Hypothesis makes it easier by generating all of these tests (and more)
automatically.

It's also unclear if my tests are really thorough.
I haven't included:
- any lists with negative numbers
- any lists with both floats and integers
- any lists with repeated elements
"""

"""
The idea of Hypothesis: instead of running a long list of specific
examples, randomly generate thousands or tens or hundreds of thousands
of examples.

This is called "random testing".

    Note: "fuzzing" is a form of random testing -- very common technique in computer security

Advantages:
- More likely to find a bug (assertion violation) if one exists
- Allows to test more general specifications, not just specific input
  and output examples.
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

# This example generates input lists of integers
# @pytest.mark.skip
@given(st.lists(st.integers()))
def test_list_product(xs):
    # Unit examples
    # assert list_product([]) == 1
    # Not very interesting!
    # More interesting: check that our implementation
    # matches the standard/expected implementation.

    # a form of spec: checking whether one program is equivalent to another
    assert list_product(xs) == reduce(lambda x, y: x * y, xs, 1)

# pytest 1-specificcations.py passed - our implementation is correct!

# (at least, on all of the inputs that Hypothesis tried.)

# Internally: will generate like
# def test___hypothesis_wrapper_test_list_product():
#     # generate a bunch of random inputs
#     for xs in input_examples:
#         run test_list_product(xs)
#         if error: return error
#     return Ok

"""
One important point for now:
Ties back to the question earlier:

    Q: If we can't find a counterexample to the specification for a program,
    does that mean the program satisfies the specification?

    A:
        If we test **all possible inputs**, then yes!
        If we only test **some** possible inputs, then no.

    Important point: Hypothesis only tests some inputs, not all!
    (We will see that the tools we cover later actually cover all inputs:
     Z3 and Dafny will be able to check whether the specification holds on
     all inputs.)

    This is what makes Hypothesis a **testing** tool, rather than **verification.**
"""

"""
=== Recap ===

1. We defined a "program specification" as any true or false property of a program

2. We are agnostic to how specifications are written, but in this class we are generally
   interested in "formal specifications" - we can run/test them, they are formally
   defined in logic.

3. Hypothesis can be used to, given input a program and a specification, determine whether the spec seems to hold on a bunch of random inputs
(useful for software testing)

4. Difference between testing & verification: Testing = try some inputs, verification (where we're eventually going) = actually determine whether the spec holds on **all** inputs, not just some inputs.

=== A philosophical point ===

Recall from lecture 0:
To determine if our code is correct, we need a specification!

    remember the car example and chess program (Stockfish) examples!
    What does it mean for a program to be "correct"?
    Our answer is that it *can't* mean anything, unless there is some
    definition of what it *means* to be correct.
    That definition is the specification.

After all, when your boss/teacher/colleague/friend asks you to
write a program, they probably have some particular expectation
in mind of what that program should do.
If we write the expectation down in a precise way, then we get
a specification.
"""
