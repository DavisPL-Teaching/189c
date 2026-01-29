"""
ECS 189C
Lecture 2, part 2:
Logic programming

=== Intro ===

In part 1, we saw that Z3 is useful for proving that a spec holds
- not just on one input, on all inputs!

- paradigm shift from testing to verification

    testing = check the spec on some specific inputs (Hypothesis)
    verification = prove the spec on all inputs. (Z3, Dafny)

We will see in this lecture that Z3 is more general than that.

It's actually a tool which can be used in two complementary,
dual paradigms:

    Proof      and       Satisfiability.
    prove()              solve()

(Aside for those who have taken a logic class: proof = validity)

In this part:

- Satisfiability
- z3.solve() and z3.prove()
- Basic data types: Bool, Int, Real

Along the way:

- More practice with how Z3 variables and formulas work.
"""

"""
Poll
We'll do this one as a class.

The z3.prove function (or our custom prove function)
returns one of three results:
- PROVED - proved (demonstrate that it's true for all inputs)
- COUNTEREXAMPLE - counterexample (shows an input where the spec is not true)
- UNKNOWN - failed to prove (this basically means "I don't know")

What would you guess is the output of the following Z3 code?
"""

import z3
import pytest
from helper import prove, PROVED, COUNTEREXAMPLE, UNKNOWN

# @pytest.mark.skip
# @pytest.mark.xfail
def test_poll_output():
    x = z3.Int('x') # Define x to be an input integer
    y = z3.Int('y') # Define y to be an input integer
    spec = z3.And(x > 100, y < 100) # Assert spec: x > 100 and y < 100

    # prove(spec) # will return PROVED, COUNTEREXAMPLE, or UNKNOWN

    assert prove(spec) == COUNTEREXAMPLE

# Uncomment to run
# test_poll_output()

"""
A) "proved"
B) "failed to prove"
C) "counterexample" with no other text
D) "counterexample" together with an example of x and y

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

```
counterexample
[y = 100, x = 101]
```

Key point: "proved" means it must be true for all inputs.

Change to solve() instead of prove()
"""

from helper import solve, SAT, UNSAT, UNKNOWN

def test_poll_output_2():
    x = z3.Int('x') # Define x to be an input integer
    y = z3.Int('y') # Define y to be an input integer
    spec = z3.And(x > 100, y < 100) # Assert spec: x > 100 and y < 100

    # Is the spec true for all inputs?
    # prove(spec) # will return PROVED, COUNTEREXAMPLE, or UNKNOWN

    # Is the spec true for **at least one** input?
    solve(spec)

    # assert prove(spec) == COUNTEREXAMPLE

# Uncomment to run
test_poll_output_2()

"""
Unlike prove(), solve() gave us back an example where the spec was *true* (just one particular input),
rather than giving us a counterexample where the spec was false.

We'll see that this can be used for many useful and fun applications.

****** where we ended for Tuesday, January 27 ******
"""

#############################################################

"""
Recap from last time:

- Z3 can be used to prove a spec on all inputs

    (Testing -> Verification)

- Z3 requires us to rewrite the code in Z3.

===== Before we continue! (Very important!) =====

Two pitfalls:

- Z3 variables are different than Python variables!

- Z3 expressions do not evaluate - they are mathematical formulas

Let's do another exercise to see this.

Exercise:
The ReLU function is sometimes used as an activation function in neural networks.
If the input is positive it returns x, otherwise 0.

Use Z3 to prove that applying ReLU twice is the same as applying ReLU once.
"""

def relu(x):
    # TODO
    raise NotImplementedError

def relu_z3(x):
    # TODO
    raise NotImplementedError

@pytest.mark.skip
def test_prove_relu():
    # TODO
    raise NotImplementedError

"""
Print out the output after some intermediate steps. What happens?

Different than using Hypothesis and Python assertions!

What would happen if we tried to use Python assertions above?
"""

"""
=== Poll ===

1. Which of the following are correct difference(s) between a z3.Int and a Python integer? (select all that apply)

2. Which of the following is a good reason to use a Z3 variable instead of a Python variable? (select all that apply)

https://forms.gle/8UzzcAPHXQK9Pzkv8

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

Let's dive in to more about how Z3 works.
"""

"""
===== Satisfiability =====

To understand how Z3 works, we need to understand the concept
of satisfiability.

A *formula* is a logical or mathematical statement that is either true or false.
Formulas are the main subject of study in logic and they are also
the core objects that Z3 works with.

Examples:

    1. "x > 100 and y < 100"
    2. "x * x = 2"
    3. "x is an integer"
    4. "If Socrates is human, then socrates is mortal"

Essence of satisfiability:

A formula is *satisfiable* if it is true for *at least one* input.

Examples:

    1.

    2.

    3.

    4.

Key point:

    Satisfiable == True for at least one input.

Side note:
If you've taken ECS 120, you may have seen the Boolean satisfiability problem,
or SAT or 3SAT, and this is an example of what I'm calling Satisfiability.

Let's start with boolean variables. Using Z3:

To make a Boolean variable, we use:
- z3.Bool
- z3.Bools
"""

# a = z3.Bool('a')
# b = z3.Bool('b')

# This defines two boolean variables, a and b.
# We'll see what the 'a' and 'b' mean in a moment

"""
Creating a formula

We can take our boolean variables and combine them
"""

# form1 = z3.And(a, b)
# form2 = z3.Or(a, b)
# form3 = z3.Not(a)
# form4 = z3.And(z3.Or(a, b), z3.Or(a, z3.Not(b)))

# We could run z3.prove() on these formulas or a new function called
# z3.solve() -- we will do this in a moment

"""
Questions:

- Why does the variable have to be named?
I.e., why did I write
    a = z3.Bool('a')
instead of just z = z3.Bool() ?

A: this is just how z3 works -- it uses the name, NOT the Python variable name,
to determine the identify of a variable.

x = z3.Bool('a')
y = z3.Bool('a')
# ^^ These are actually the same variable, in Z3

x = z3.Bool('y')
# ^^ the variable name here, in Z3, is 'y', not x.

- What is the type of a and b?

It's a z3.Bool type, (not the same as a Python boolean)

- Why aren't a and b just normal booleans?

This goes to the thing about Z3 working with a model of the program.
Z3 needs to know what are the symbols in a formula and what do they mean,
NOT just the true-or-false output.

a = True
b = False
a and b ====> False
But Z3 wouldn't be able to see what the formula is and what it means.

Z3 needs a formula object, not just a Python boolean.

- Why do we need to ues z3.And and z3.Or instead of just "and" and "or"?

Same reason: Z3 needs a formula in the end, not just the final result.
"""

"""
Checking satisfiability

We can use the z3.solve() function to check if a formula is satisfiable.
This is what all of Z3 is based on!

There are three possible outcomes:
- z3.sat =====> Yes the formula is satisfiable
- z3.unsat =====> No the formula is not satisfiable
- z3.unknown =====> I don't know

Note: If this seems similar to the "prove" function from earlier, it should!
We will discuss how prove is implemented shortly.

Recall:
form1 = z3.And(a, b)
form2 = z3.Or(a, b)
form3 = z3.Not(a)
form4 = z3.And(z3.Or(a, b), z3.Or(a, z3.Not(b)))
"""

# z3.solve(form1)
# z3.solve(form2)
# z3.solve(form3)
# z3.solve(form4)
# # =====> Satisfiable, Z3 gives an example

# # For all four examples, the formula is satisfiable -- Z3 returns an example
# # where the formula is true.
# # What about something that's NOT satisfiable?

# form5 = z3.And(a, z3.Not(a))
# # A and Not A --> always false, should be never true, i.e. not satisfiable

# z3.solve(form5)
# # =====> Unsatisfiable, Z3 says "no solution"

"""
Two functions of Z3:
z3.prove --> ask if something can be proven
z3.solve --> ask if something is satisfiable

Actually, how does z3.prove work?
If I run z3.prove(formula)
it calls
z3.solve(z3.Not(formula))
- If satisfiable: that means there is an input where "NOT formula" is true
    Therefore, "formula" must be false (on that input)
    Therefore, "formula" is not necessarily true for all inputs, i.e. it's not
    provable -- there is a counterexample.
- If unsatisfiable: that means there are no inputs where "NOT formula" is true
    Therefore, "NOT formula" is false for all inputs
    Therefore, "formula" is true for all inputs
    Therefore, formula is provable.
- If unknown: we return unknown.

In essence: provability and satisfiability are reducible to each other
Specifically: provability of "P" and satisfiability of "Not P" are solving
the same problem.

When does z3.solve (or z3.prove) return unknown?
Intuitively, if the formula is really mathematically complex, involves a lot
of difficult operations and it's too hard to figure out whether it's satisfiable
or not.
--> Booleans are quite easy, so this will rarely happen with booleans.

=== Summary: z3.prove vs. z3.solve ===

When should you use z3.prove vs z3.solve?

- z3.prove tries to show that the spec holds for all
    values of the variables

    + useful for: proving specifications, and also when
    you want to show that some assertion or some property always holds

- z3.solve tries to show that the
    spec holds for one particular assignment of values to the variables.

    + useful for: solving equations, solving puzzles, and
    similar tasks where you have some set of constraints, and
    you want to find a solution to those constraints.
    E.g.: you want to solve x^2 - 3x + 2 = 0
    or you want to solve a Sudoku puzzle

We also saw that these are really the same thing under the
hood. In fact they use something called a Solver API
Under the hood:

    z3.Solver

which you can create to solve arbitrary formulas. (See the helper.py file
for how to use the Solver API.)

=== Boolean operations ===

What boolean operations can we use?

- z3.And
- z3.Or
- z3.Not
- z3.Implies
- z3.If
- z3.Xor

These are all standard functions on boolean numbers, but instead of evaluating
the operation, they create a formula.

The reason they have to create a formula is because Z3 wants to determine
if the formula is true for ANY input (satisfiability) or for ALL inputs (provability)
not necessarily just evaluate it on a single input.

Examples:

"""

# print("More examples:")
# x = z3.Bool('x')
# y = z3.Bool('y')
# # What does implies do?
# z3.solve(z3.Implies(x, y))
# # Implies is basically the "if then" function and it has the following meaning:
# # if x is true then y, otherwise true.
# # arrow (-->)
# # If you like you can write z3.If(x, y, True) instead of z3.Implies(...)
# # It's reducible to if then.

# # XOR implies or?
# # XOR is exclusive or (exactly one, but not both of x and y are true)
# x_xor_y = z3.Xor(x, y)
# x_or_y = z3.Or(x, y)
# z3.prove(z3.Implies(x_xor_y, x_or_y))

"""
Convenient shortcuts:

- Equality (==)
- z3.And([...])
- z3.Or([...])

You can directly write x == y
for booleans, and Z3 knows what that means
You can also write
z3.And([formula1, formula2, formula3, ...])
for a list of formulas and it will create an "and" expression of all of them.
Similarly for Or.

These are just shortcuts, and can be implemented using the above operations already.
"""

"""
=== Common confusion: Z3 variables versus Python variables ===

We've seen this notation come up in Z3:
b = z3.Bool('b') <---- this is a variable, i.e. an input
x = z3.Int('x') <---- this is a variable, i.e. an input

Q: x = z3.Int('x')
Does x have to match the string?
A: No. Z3 will use the string to determine the variable.
y = z3.Int('x') # This is also the same variable as x

"""

####################
###     Poll     ###
####################

# What would you guess is the output of the following Z3 code?

# @pytest.mark.skip
# def test_poll_output_2():
#     x = z3.Int('x')
#     y = z3.Int('y')
#     spec = z3.Implies(z3.And(x >= 10, y == x * x), y >= 100)
#     prove(spec)

# print("Output:")
# test_poll_output_2()

# Let's try it out

########################
###    Data Types    ###
########################

"""
The power of Z3 is in its ability to work with more complex data types
(not just booleans).

Basic data types: Bool, Int, Real

(In fact we don't really need booleans -- we can represent them as integers.)
"""

# # How to define a boolean using integers
# b = z3.Int('b')
# boolean_spec = z3.And(b >= 0, b <= 1)
# z3.solve(boolean_spec)
# # If you wanted to do boolean operations,
# # and, or, implies, etc. you could define these on integers.

"""
=== Integers ===

z3.Int
z3.Ints -- creates multiple integers

Examples
"""
# x, y = z3.Ints("x y")
# spec = z3.And(x > y, y > 5)
# z3.solve(spec)

"""
What operations are supported here?
You can use most built-in integer operations in Python
on Z3 integers. BUT keep in mind it's not the same as Python
integer arithmetic.
"""

# x + y # <- Z3 expression, NOT a Python integer
# print(x + y) # Prints as "x + y", not as some specific integer

# # Problem: find two integers whose sum and product is the same.
# print("Find two integers whose sum and product is equal:")
# z3.solve(x + y == x * y)

# Operations we've seen so far: +, *, ==, <, all of these
# work on Z3 integers.

"""
We can use functions to wrap up useful functionality.

For example:
Define a Pythagorean triple as three positive integers a, b, c
such that a^2 + b^2 = c^2.

Q1: Find a pythagorean triple.
Q2: Find a pythagorean triple with a = 5.

It's often useful to define a function which abstracts the
behavior you're interested in.
"""

def pythagorean_triple(a, b, c):
    # We can just return the expression a^2 + b^2 = c^2
    # return (a * a + b * b == c * c)
    # Debugging: we can add the additional constraints
    # that we forgot here
    pythag_constraint = a * a + b * b == c * c
    a_is_positive = a > 0
    b_is_postive = b > 0
    c_is_positive = c > 0
    return z3.And([
        pythag_constraint,
        a_is_positive,
        b_is_postive,
        c_is_positive,
    ])
    # Here: the other constraints are silently ignored :(
    # What's happening here?
    # Python boolean operators (and/or) are defined for arbitrary
    # data types. And "falsey" datatypes are treated as false
    # and "truthy" datatypes are treated as true
    # and/or are both short circuiting so they'll return
    # the first value that is either false/true, respectively.
    # Bottom line here: this doesn't work because "and" already
    # has a definition in Python.
    # This is not what we want.
    # return (pythag_constraint and a_is_positive and b_is_postive and c_is_positive)
    # TL;DR Python boolean operators are weird, so be careful with them.

# If we want an example:
# a, b, c = z3.Ints("a b c")
# print("Example pythagorean triple:")
# z3.solve(pythagorean_triple(a, b, c))

"""
Q: what if we want more than one answer?

We can try rerunning...

The easiest way is a common technique where
each time we get an answer, we add an assertion that
that answer is excluded.
"""

# First answer: a = 6, b = 8, c = 10
# Second answer
# new_constraint = z3.Or(
#     z3.Not(a == 6),
#     z3.Not(b == 8),
#     z3.Not(c == 10),
# )
# # ^ Force the solver to give us a new answer.
# z3.solve(z3.And([
#     pythagorean_triple(a, b, c),
#     new_constraint,
# ]))

# We can keep adding constraints for each new answer,
# there is also a way to do this programmatically
# (This will use the Solver API that we will shortly see.)
# We will see how to write a wrapper around Solver to do this.

"""
=== Recap ===

Formula = Mathematical statement that can be true or false

A formula is *satisfiable* if it is true for at least one input.

How Z3 works:

- Solve satisfiability by running solve(formula)

- To find a proof of spec, just run solve(z3.Not(spec)) !

A last question:
How does this help us prove specifications?

Remember that for a program my_prog, we defined preconditions and postconditions,
and the "spec" was the property that if the precondition holds, then the postcondition
must hold.

Usually we translate this to a Z3 spec by writing

    x = Input(..)
    y = my_prog(x)

Then we can write the formula:

    z3.Implies(precondition(x), postcondition(y))

If Z3 is able to prove this, then the spec holds -- the property is true for all inputs.
"""
