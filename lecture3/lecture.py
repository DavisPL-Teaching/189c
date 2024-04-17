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
reader (or a computer) that the conclusion must be true.

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
    # Read this as: if x < 0 then -x else x.
    return z3.If(x < 0, -x, x)

# Notice this is exactly the same function as before,
# but written in a different way, now with z3.If.

# To see output:
# run with pytest lecture.py -rP
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
    prove(spec)

# What happens if the spec does not hold?

@pytest.mark.xfail
def test_absolute_value_z3_2():
    x = z3.Int('x')
    y = absolute_value_z3(x)
    # This spec is wrong -- it says that abs(x) should
    # always be positive (not just nonnegative)
    spec = z3.And(z3.Or(y == x, y == -x), y > 0)
    # What happens when we try to prove it?
    prove(spec)

# Z3 tells us that it's not true -- and
# shows us a counterexample:
# counterexample
# [x = 0]

"""
What's happening here?

Z3 is interpreting the spec as a mathematical statement,
and trying to come up with either a proof that it's always true
or a counterexample.

Differences from Hypothesis?

1. Random test case vs. proof

Hypothesis just runs random examples, Z3 thinks about the program
mathematically and tries to analyze "all" examples.

2. We had to rewrite the function using Z3!

For absolute_value, it was just a standard Python function
For Z3, we had to rewrite it as absolute_value_z3, using Z3 abstractions.

==> we are testing a *model* of the program, not the program itself!

Why are we testing a model?
Well, Z3 thinks about things formally and mathematically.
So it needs a description of the program that is fully mathematical.
- In principle, any program can be translated to the right model.
- In principle, this is often possible to do automatically.
But, that doesn't mean that the tool to do that is always easily available now.

Example: we have z3.If, so if your program has if statements,
we can encode it in Z3.
But the developers of Z3 may not have written equivalents for every
Python funciton. (Ex.: files, print(), ...)
And in those cases, you would need to write your own model.

Using a model is both a strength and a weakness.

- Other differences? (We will see later)

Recap:
We saw that Z3 can do what Hypothesis can't do: prove that the spec
is correct: true for ALL inputs, not just some inputs.

We discussed how to write a basic example in Z3, and how Z3 requires
a model of the program, not the program itself

We will get into more specific syntax + data types in the rest of
this week.

########## Where we left off for Day 6 ##########

Day 7

=== Announcements ===

- HW1 due Friday (in 2 days!)
    + Start now if you haven't already! (HW1 invite link in Piazza)
    + 1 of you still has an unlinked GitHub account -- please re-click the invite

- Submit HW0 if you haven't yet (5 people)
    + No due date but will make it difficult to complete HW1 unless you catch
      problems now

- General notice: encourage posting questions on Piazza

=== Plan for today ===

First part:
- Clearing something up from last time
- Poll

Main material:
- Satisfiability
- z3.solve() and z3.prove()
- Basic data types: Bool, Int, Real

Questions?

=== Clearing something up ===

Z3 is not just useful for proving properties of "mathematical" functions.

- In fact, programs in any language are just mathematical functions!

- Compilers also work with a model of the program!
    That is how they are able to optimize code prior to running it.

- Applications
"""

####################
###     Poll     ###
####################

"""
The z3.prove function (or our custom prove function)
returns one of three results:
- proved
- failed to prove (this basically means "I don't know")
- counterexample (shows a case where the spec is not true)

What would you guess is the output of the following Z3 code?
"""

@pytest.mark.skip
def test_poll_output():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.And(x > 100, y < 100)
    prove(spec)

"""
A) "proved"
B) "failed to prove"
C) "counterexample" with no other text
D) "counterexample" together with an example of x and y

https://forms.gle/Q533T9gUhgQUabAu9
https://tinyurl.com/bdcrceep

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
.
.
.
.
.

(Try running it)

Key point: "proved" means it must be true for all inputs.

How does Z3 work?

Before we understand how Z3 works, we need to understand the concept
of satisfiability.
"""

##########################
###   Satisfiability   ###
##########################

"""
A *formula* is a logical or mathematical statement that is either true or false.
Formulas are the main subject of study in logic and they are also
the core objects that Z3 works with.
Examples:
...

Essence of satisfiability:

A formula is *satisfiable* if it is true for *at least one* input.

Examples:
...

Let's start with boolean variables. Using Z3:

- z3.Bool
- z3.Bools
"""

a = z3.Bool('a')
b = z3.Bool('b')

"""
Creating a formula
"""

"""
Variable naming
"""

"""
Questions:

- Why does the variable have to be named?

- What is the type of a and b?

- Why aren't a and b just normal booleans?

- Why do we need to ues z3.And and z3.Or instead of just "and" and "or"?
"""

"""
Checking satisfiability

We can use the z3.solve() function to check if a formula is satisfiable.
This is what all of Z3 is based on!

There are three possible outcomes:
- z3.sat
- z3.unsat
- z3.unknown

Note: If this seems similar to the "prove" function from earlier, it should!
We will discuss how prove is implemented shortly.
"""

"""
What boolean operations can we use?

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
The power of Z3 is in its ability to work with more complex data types
(not just booleans).

Basic data types: Bool, Int, Real

(In fact we don't really need booleans -- we can represent them as integers)
"""

"""
=== Integers ===
"""

"""
Z3 can even work with data types that are not available in Python.
Here is an interesting one:

=== True Real Numbers ===

z3.Real
"""

"""
More advanced data types:
- Functions
- Arrays and sequences
- Strings and regular expressions
"""
