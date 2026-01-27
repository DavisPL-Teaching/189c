"""
Lecture 2: Z3 and Satisfiability
ECS 189C

Part 1: Introduction to Z3
"""

####################
###     Poll     ###
####################

"""
Which of the following is a limitation of testing with Hypothesis?
(Select all that apply)

1. Testing can only demonstrate the presence of bugs, and can never prove their absence.
2. The specification written could be wrong (not what the user intended)
3. The specification written could be incomplete (underspecified)
4. It can only test preconditions and postconditions
5. It can only test assume and assert statements

https://forms.gle/Vy9dAd7G31YyY7TE6

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

"""

#######################
###   Intro to Z3   ###
#######################

"""
Recap:

- We've learned about writing specifications

    + Ways to write specifications: precondtions, postconditions, assume, assert

- Hypothesis uses random testing (also known as property-based testing) to generate test cases

- Hypothesis is limited to finding bugs; it can't prove the specification holds for all inputs.

Example:
"""

def absolute_value(x):
    # Def of absolute value?
    # (This is what the built-in abs function does)
    if x < 0:
        return -x
    else:
        return x

# In Hypothesis, we could write a specification for the function like this:

from hypothesis import given
import hypothesis.strategies as st
import pytest

@pytest.mark.skip
@given(st.integers())
def test_absolute_value(x):
    y = absolute_value(x)
    assert y == x or y == -x
    assert y >= 0

# What happens when we test it?

# It passes -- it seems to work for a bunch of random examples.

# What if we want to prove that the function is correct for all inputs?
# We could try increasing the number of test cases...

from hypothesis import settings

@pytest.mark.skip
@given(st.integers())
# Uncomment for slow test running many examples
# @settings(max_examples = 10000)
def test_absolute_value_more_examples(x):
    y = absolute_value(x)
    assert y == x or y == -x
    assert y >= 0

"""
=== A better way ===

Let's *prove* that the function is correct for all inputs using Z3.

Recall:
A proof is a rigorous mathematical argument that convinces the
reader (or a computer :-) ) that the conclusion must be true.

A statement which has been proven is called a theorem.

What is Z3?

An automated theorem prover (from Microsoft Research)
You input a mathematical statement (mathematical formula)
If it's true, Z3 will prove it.
It tries to do this fully automatically.
    - (Not always successfully, as we will later see.)

First step: we need to have Z3 installed

(You've done this on HW0)

And, we need to import it
"""

# See HW0 -- pip3 install z3-solver
import z3

# Helper file with some helper functions - ignore for now
from helper import prove, PROVED, COUNTEREXAMPLE

"""
Second step: we have to rewrite the function using Z3.

- [Z3 introduction](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)
- [Z3 docs](https://ericpony.github.io/z3py-tutorial/guide-examples.html)
"""

def absolute_value_z3(x):
    # Read this as: if x < 0 then -x else x.
    return z3.If(x < 0, -x, x)

# Notice this is exactly the same function as before,
# but written in a different way, now with z3.If.

# To see output:
# run with pytest lecture.py -rP
@pytest.mark.skip
def test_absolute_value_z3():
    # Declare our variables
    x = z3.Int('x')
    y = absolute_value_z3(x)
    # Spec:
    # y is either equal to x or -x, and y is nonnegative
    spec = z3.And(z3.Or(y == x, y == -x), y >= 0)
    # Ask Z3 to prove it:
    # This is our custom helper function
    # You can also just use z3.prove here
    # z3.prove will print stuff out to std output but won't
    # assert anything
    # but I wrote a version that works inside a unit test
    assert prove(spec) == PROVED

# What happens if the spec does not hold?

@pytest.mark.skip
# @pytest.mark.xfail
def test_absolute_value_z3_2():
    x = z3.Int('x')
    y = absolute_value_z3(x)
    # This spec is wrong -- it says that abs(x) should
    # always be positive (not just nonnegative)
    spec = z3.And(z3.Or(y == x, y == -x), y > 0)
    # What happens when we try to prove it?
    assert prove(spec) == PROVED

# Z3 tells us that it's not true -- and
# shows us a counterexample:
# counterexample
# [x = 0]

"""
What's happening here?

Z3 is interpreting the spec as a mathematical statement,
and trying to come up with either a proof that it's always true
or a counterexample.

=== So it's all about math? ===

Z3 is not just useful for proving properties of "mathematical" functions.

We will see that properties of practical programs and problem domains
can be fruitfully encoded using mathematical formulas.

Examples:

- Programs in any language are just mathematical functions!

- Compilers also work with a model of the program!
    That is how they are able to optimize code prior to running it.

- Many real-world software systems, like cloud services,
    distributed systems, compilers, system implementations, etc.
    can be modeled as mathematical objects
    (state spaces with some transition relation)

- One well-known example: Amazon AWS uses Z3 to model who has access
    to cloud resources - we encode "who has access" as a mathematical property,
    then we want to prove whether or not an unauthorized user has access.

The key to applying Z3 in the real world is to define the right
mathematical domain to map your programs to.

=== Conclusions ===

Differences from Hypothesis?

1. Random test case vs. proof

    Hypothesis just runs random examples, Z3 thinks about the program
    mathematically and tries to analyze "all" examples.

2. We had to rewrite the function using Z3!

    For absolute_value, it was just a standard Python function
    For Z3, we had to rewrite it as absolute_value_z3, using Z3 abstractions.

    One way to think about it:
    we are testing a *model* of the program, not the program itself!

    More on this later! This is both an advantage and a drawback.

3. Other differences? (We will see later)

Recap:

We saw that Z3 can do what Hypothesis can't do: prove that the spec
is correct: true for ALL inputs, not just some inputs.

We discussed how to write a basic example in Z3, and how Z3 requires
us to rewrite the program using Z3 syntax

Things we will see next:

- Z3 is much more powerful than just proving properties of programs.

- More specific syntax and data types

- Z3 internals & "how it works".
"""
