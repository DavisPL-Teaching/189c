"""
Lecture 3: Z3 and Satisfiability
ECS 189C
April 15, 2024
"""

####################
###     Poll     ###
####################

"""
Which of the following is a limitation of testing with Hypothesis? (Select all that apply)

1. Testing can only demonstrate the presence of bugs, and can never prove their absence.
2. The specification written could be wrong (not what the user intended)
3. The specification written could be incomplete (underspecified)
4. It can only test preconditions and postconditions
5. It can only test assume and assert statements

https://forms.gle/gxJjhhbr1qDSmqeS8
https://tinyurl.com/3dxdd5rn
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
    # TODO
    raise NotImplementedError

# In Hypothesis, we could write a specification for the function like this:

from hypothesis import given
import hypothesis.strategies as st
import pytest

@given(st.integers())
@pytest.mark.skip
def test_absolute_value(x):
    # TODO
    raise NotImplementedError

# What happens when we test it?

# What if we want to prove that the function is correct for all inputs?
# We could try increasing the number of test cases...

@given(st.integers())
@pytest.mark.skip
def test_absolute_value_better(x):
    # TODO
    raise NotImplementedError

"""
=== A better way ===

Let's *prove* that the function is correct for all inputs using Z3.

Recall:
A proof is...

What is Z3?

First step: we need to have Z3 installed
and we need to import it
"""

# Need to have z3 installed
# See HW0 -- pip3 install z3-solver
import z3

# This helper function is also useful.
# You can ignore it for now -- it is a modified
# version of z3.prove from the z3 library.
# We will learn what this syntax means later.
# A similar function will be provided in the homework.
def prove(spec):
    ### Ignore ###
    s = z3.Solver()
    s.add(z3.Not(spec))
    r = s.check()
    if r == z3.unsat:
        print("proved")
    elif r == z3.unknown:
        print("failed to prove")
        print(s.model())
        assert False, "failed to prove"
    else:
        print("counterexample")
        print(s.model())
        assert False, "counterexample"

    ### End ignore ###

"""
Second step: we have to rewrite the function using Z3.

- [Z3 introduction](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)
- [Z3 docs](https://ericpony.github.io/z3py-tutorial/guide-examples.html)
"""

def absolute_value_z3(x):
    # TODO
    raise NotImplementedError

# To see output:
# run with pytest lecture.py -rP
def test_absolute_value_z3():
    # TODO
    # Spec:
    # Ask Z3 to prove it:
    raise NotImplementedError

# What happens if the spec does not hold?

def test_absolute_value_z3():
    # TODO
    raise NotImplementedError

"""
What's happening here?

Differences from Hypothesis?

- Random test case vs. proof
- We had to rewrite the function using Z3! <-- we are testing a *model*
of the program, not the program itself
- Other differences? (We will see later)

How does it work?

Before we understand how Z3 works, we need to understand the concept
of satisfiability.
"""

##########################
###   Satisfiability   ###
##########################

"""
A *formula* is a statement that is either true or false.
Formulas are the subject of study in logic and they are also
the core objects that Z3 works with.
Examples:
...

Essence of satisfiability:

A formula is *satisfiable* if it is true for *at least one* input.

Example:
...

Let's start with Boolean formulas. Using Z3:

- z3.Bool
- z3.Bools
"""

"""
Creating a formula
"""

"""
Checking satisfiability

We can use the z3.solve() function to check if a formula is satisfiable.
This is what all of Z3 is based on, including our
prove() function from earlier.

There are three possible outcomes:
- z3.sat
- z3.unsat
- z3.unknown
"""

"""
What Boolean operations can we use?

- z3.And
- z3.Or
- z3.Not
- z3.Implies
- z3.If
- z3.Xor

Examples:
"""

"""
Convenient shortcuts:

- Equality (==)
- z3.And([...])
- z3.Or([...])
"""

"""
=== Recap ===

We know what a formula is.
Satisfiability is the property of a formula being true for at least one input.

How does this help us prove specifications?
"""

########################
###    Data Types    ###
########################

"""
The power of Z3 is in its ability to work with additional data types.
"""

"""
=== Integers ===
"""

"""
Z3 can even work with data types that are not available in Python.
Here is an interesting one:

=== True Real Numbers ===
"""

"""
More advanced data types:
- Functions
- Arrays and sequences
- Strings and regular expressions
"""
