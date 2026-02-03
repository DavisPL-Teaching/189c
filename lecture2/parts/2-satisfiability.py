"""
ECS 189C
Lecture 2, part 2:
Satisfiability

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
# test_poll_output_2()

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

    f(x):
    If the input x is positive it returns x, otherwise 0.

                      /
                     /
                    /
                   /
    ______________/

Use Z3 to prove that applying ReLU twice is the same as applying ReLU once.
"""

def relu(x):
    if x > 0:
        return x
    else:
        return 0

def relu_z3(x):
    return z3.If(x > 0, x, 0)

# @pytest.mark.skip
def test_prove_relu():

    # Define the input x -- represents all possible inputs
    x = z3.Int("x")

    # Define the spec -- applying ReLU twice == applying once
    spec = relu_z3(relu_z3(x)) == relu_z3(x)

    # Prove the spec
    assert prove(spec) == PROVED

"""
(Note: z3.If(x > 0, x, 0)

    what's happening here - Python integer 0 is being converted
    to a Z3 integer expression 0.

    ===> We can convert Python integers/expressions to Z3
         integers/expressions, but not the other way around.

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
    2. "x * x == 2"
    3. "x is an integer"
    4. "If Socrates is human, then socrates is mortal"

Definition of satisfiability:

    A formula is *satisfiable* if it is true for *at least one* input.

    (This is the solve() function we saw last time)

Examples
Which of 1-4 is satisfiable?

    1. That is satisfiable because it is true for at least one input:

        ex.: x == 101 and y == 50

        True for at least one input ====> Satisfiable.

    2. (assume x is an integer)

        Not satisfiable for an integer x, but if x was a real number,
        we could do x = sqrt(2)

        ====> Unsatisfiable if x is an integer,
              Satisfiable if x is a real number.

    3. Yes, take x = 3

        ====> Satisfiable if x is an integer (take x = 3)
        ====> Satisfiable if x is a real number variable (take x = 3)

    4. Yes, satisfiable

        Socrates is human = boolean value True

        Socrates is mortal = boolean value True

        "If true then true" which is true

        ====> Satisfiable.

Other examples:

    True ====> Satisfiable

    False ====> Unsatisfiable

    False implies False
    (if False then False)
        ====> True, therefore satisfiable.

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

a = z3.Bool('a')
b = z3.Bool('b')

# a, b = z3.Bools("a b")

"""
Creating a formula

We can take our boolean variables and combine them
"""

form1 = z3.And(a, b)
form2 = z3.And(a, b, a)
form3 = z3.Or(a, b)
form4 = z3.Not(a)
form5 = z3.And(z3.Or(a, b), z3.Or(a, z3.Not(b)))

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

    x = z3.Int("var1")

    ^^^^^ not recommended, but possible

    x = z3.Int("x")

    ^^^^^ recommended style

    x = z3.Bool('a')
    y = z3.Bool('a')
    # ^^ These are actually the same variable, in Z3

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
=== Checking satisfiability ===

We can use the z3.solve() function to check if a formula is satisfiable.
This is what all of Z3 is based on!

There are three possible outcomes:
- z3.sat =====> Yes the formula is satisfiable
- z3.unsat =====> No the formula is not satisfiable
- z3.unknown =====> I don't know

Recall two functions of Z3:
    z3.prove --> ask if the spec can be proven (for all inputs)
    z3.solve --> ask if the spec is satisfiable (for at least one input)

Note!

    prove(spec) returns PROVED, COUNTEREXAMPLE, or UNKNOWN

        ... but PROVED is just an alias for UNSAT and
            COUNTEREXAMPLE is just an alias for SAT!

        How can this be?

    Solving whether a spec is true on all inputs, is the
    same thing as solving satisfiability for

        Not(spec).

    Let's think about this...

        If spec is true on all inputs ...

            ... then Not(spec) is false on all inputs

            ... so solve(Not(spec)) returns UNSAT.

        If spec is NOT true on all inputs ...

            ... then it is false for at least one input

            ... so Not(spec) is true for at least one input

            ... so solve(Not(spec)) return SAT.

    Therefore,

        prove(spec)

    is truly just the same thing as

        solve(not(spec)).

This is how prove is internally implemented.

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
====== Recap =====

We learned about common pitfalls working with Z3

    Z3 vars are different than Python vars

    You can go from Python to Z3, but not vice versa

    Z3 expressions like == and >
    are just symbols - they are not evaluated.

We got some more practice with working with Z3 and writing
Z3 specs

    1. define your variables

    2. define formulas - write the spec

    3. solve the spec or prove the spec

We learned about satisfiability

    A formula is satisfiable (SAT) if it is true on
    **at least one** input

We learned more about z3.prove/z3.solve (or prove/solve)

    Internally, prove(spec) just calls solve(z3.Not(spec))

****** where we ended for Thursday, January 29 ******

==============================
"""

###################################
###    Additional Operations    ###
###################################

"""
We will go through this quickly, some you can review on your own time.

=== Boolean operations ===

z3.Bool type

What boolean operations can we use?

- z3.And
- z3.Or
- z3.Not
- z3.Implies
    Implies(p, q) as "if p then q"
        also equivalent to: "if p then q else True"
- z3.If
    If(P, c1, c2) means "if P then c1 else c2"
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

Typical pattern:

    constraints = []

    for ...
        constraints.append(formula)

    # constraints is some list of constraints

    constraint = z3.And(constraints)

Note:

    z3.And can also accept 3 or more arguments.

You can directly write x == y
for booleans, and Z3 knows what that means
You can also write
z3.And([formula1, formula2, formula3, ...])
for a list of formulas and it will create an "and" expression of all of them.
Similarly for Or.

These are just shortcuts, and can be implemented using the above operations already.
"""

###################################
###    Additional Data Types    ###
###################################

"""
The power of Z3 is in its ability to work with more complex data types
(not just booleans).

Basic data types: Bool, Int, Real

Also goes beyond: Z3 supports arrays, strings, trees, functions, ...
    We will not cover these in Lecture 2, but I plan to cover some of them
    in Lecture 3.

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
z3.Ints -- creates multiple integers (usually not needed)

Examples
"""
# x, y = z3.Ints("x y")
# spec = z3.And(x > y, y > 5)
# z3.solve(spec)

"""
What operations are supported here?

Most built-in integer operations in Python have Z3 equivalents.

(BUT it's not the same as Python integer arithmetic!)

"""

# x + y # <- Z3 expression, NOT a Python integer
# print(x + y) # Prints as "x + y", not as some specific integer

# # Problem: find two integers whose sum and product is the same.
# print("Find two integers whose sum and product is equal:")
# z3.solve(x + y == x * y)

# Operations we've seen so far: +, *, ==, <, all of these
# work on Z3 integers.

"""
An application for Pythagorean triples is in extras/pythagorean_triples.py.

    Exercise involves the following problem:
    "Find integers a, b, c such that a^2 + b^2 = c^2"

    The file shows how to do this with z3.solve()/solve().

=== More Q+A about how Z3 works ===

Last time we saw,
In essence: provability and satisfiability are reducible to each other
Specifically: provability of "P" and satisfiability of "Not P" are solving
the same problem.

Q: When does z3.solve (or z3.prove) return unknown? (or solve/prove from helper)

    Intuitively, if the formula is really mathematically complex, involves a lot
    of difficult operations and it's too hard to figure out whether it's satisfiable
    or not.
    --> Booleans are quite easy, so this will rarely happen with booleans.

Q: When should you use z3.prove vs z3.solve? (or solve/prove from helper)

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

Q: How do these work under the hood?

    Under the hood, the helper file uses the "Solver" API:

    z3.Solver

    With the Solver API, we define a system of constraints, then
    check satisfiability with .check().

    (See helper.py)

Q: How does this help us prove specifications?

Remember that for a program my_prog, we defined preconditions and postconditions,
and the "spec" was the property that if the precondition holds, then the postcondition
must hold.

Usually we translate this to a Z3 spec by writing

    x = input (e.g. x = z3.Int("x"))
    y = my_prog(x)

Then we can write the formula:

    z3.Implies(precondition(x), postcondition(y))

If Z3 is able to prove this, then the spec holds -- the property is true for all inputs.

=== Summary ===

Formula = Mathematical statement that can be true or false

A formula is *satisfiable* if it is true for at least one input.

How Z3 works:

- Solve satisfiability by running solve(formula)

- To find a proof of spec, just run solve(z3.Not(spec)) !

"""
