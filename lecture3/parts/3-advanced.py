"""
Lecture 3, Part 3:
Advanced Z3 features

This is a shorter part. It is a brief tour of some of the other
advanced features available in Z3.
"""

import z3
from helper import solve, prove, get_solution, SAT, UNSAT, UNKNOWN

"""
===== Other data types =====

We've now seen:
- Int, bool, real, strings, and regex

Some of the other most useful types:
- Z3 arrays
- Z3 functions
"""

# More complex types have to be parameterized by a "Sort"
# Ignore this for now
I = z3.IntSort()

# Function example
x = z3.Int('x')
y = z3.Int('y')
f = z3.Function('f', I, I) # function from integers to integers
constraints = [f(f(x)) == x, f(x) == y, x != y]

# Uncomment to run
# solve(z3.And(constraints))

# anything else I should try?
# square root? Yes
# constraints = [f(f(x)) == x, f(x) == y, x != y]

# Function with two arguments?
# Yes, possible, (I don't recall the syntax at the moment)

# can we get z3 to generate the square root function?
# constraints = [f(1) == 1, f(4) == 2, f(9) == 3, f(16) == 4]

# solve(constraints)

# can we get Z3 to produce a one-to-one function?
# constraints = [f(0) == 0]
# solve(constraints)

# one_to_one = z3.ForAll([x, y], z3.Implies(x != y, f(x) != f(y)))
# solve(one_to_one)
# ^^^^^^^ too hard for Z3

# or can we make an inverse function?
# f_inv = z3.Function('f_inv', I, I)
# inverse_constraint = z3.ForAll([x], f_inv(f(x)) == x)
# solve(inverse_constraint)
# ^^^^^ also too hard

# for inputs between -10 and 10, should be one-to-one
# constraints = [
#     f_inv(f(x)) == x
#     for x in range(-10, 11)
# ]
# solve(z3.And(constraints))

# Z3 is strongly favoring if-else expressions

# Z3 is actually able to come up with a function! Not just integer
# and string values.
# We've already seen an example of this:
# Some of you noticed this div0 function on hw2. That's an example
# of Z3 coming up with a function to represent division by 0.
# x / 0 => div0(x)

# Array example
# Arrays are basically functions that take integers and return
# a value.

A = z3.Array('A', I, I)

# Uncomment to run
# solve(A[0] + A[1] + A[2] >= 0)
# ^^^^ asking for a list where the first three elements sum
# to something nonnegative

# we can store things in the array
x = z3.Int('x')

# What do you think happens when we run this :-)
# print(A[x])
# print(z3.Store(A, x, 10)) # in Python: A[x] = 10

# prove(z3.Store(A, x, 10)[x] == 10)

"""
Q: how is the array different from a list of integers?
[z3.Int("x1"), z3.Int("x2"), z3.Int("x3")]

A: difference is: Array is dynamic (can change in size),
but if we have a Python list of int variables, we are forced
to fix the number of variables up front.

In general - if you can use a 1D/2D/3D array of Int variables,
you will probably have better results than using Arrays.

===== Custom datatypes =====

You can even create your own datatypes:
"""

# TreeList = z3.Datatype('TreeList')
# Tree     = z3.Datatype('Tree')
# Tree.declare('leaf', ('val', z3.IntSort()))
# Tree.declare('node', ('left', TreeList), ('right', TreeList))
# TreeList.declare('nil')
# TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))

# Tree, TreeList = z3.CreateDatatypes(Tree, TreeList)

"""
===== The full power of Z3 =====

(This part will not be on the final)
I just want to briefly mention some of the powerful features available
in Z3 that we haven't covered in this class, in case you want to use
Z3 for your own projects.
Some of the most powerful use cases are when combining general data types
(functions and arrays) with quantifiers.

What are quantifiers?

- z3.ForAll(var_or_list_of_vars, formula)

  It states that for all possible values of the variables, formula
  should hold.
  This should be reminiscent of prove()!

- z3.Exists(var_or_list_of_vars, formula)

  It states that there exists a possible value of the variables,
  such that the formula should hold.
  This should be reminiscent of solve()!

Let's see an example:

Q: Prove that if the sum of an array is positive, then an array has
   an element that is positive.
"""

# Define the array variable
I = z3.IntSort()
array = z3.Array('array', I, I)

# First we have to express the sum of the array.
# How do we do that?
array_sum = z3.Function('array_sum', I, I)
# The value array_sum(i) will represent the sum of the values
# of the array up to index i.
constraints = []

# Base case
constraints.append(array_sum(-1) == 0)

# Inductive step -- using a ForAll constraint
# See: https://stackoverflow.com/a/31119239/2038713
i = z3.Int('i')
constraints.append(z3.ForAll(i, z3.Implies(
    z3.And(i >= 0),
    array_sum(i) == array_sum(i - 1) + array[i]
)))

# The result so far?
#    array_sum(-1) = 0
#    array_sum(0) = array[0]
#    array_sum(1) = array[0] + array[1]
#    and so on.

# Now define our problem

# Simpler version of the problem
easy_version = constraints + [array_sum(5) > 0]
precond = z3.And(easy_version)
postcond = z3.Exists(i, array[i] > 0)

# Uncomment to run
# prove(z3.Implies(precond, postcond))

# This one works.

# Interesting case:
# Z3 can prove the implication, but can't give us an example
# where the precond and postcond hold.
# solve(z3.And(precond, postcond))

# Harder version of the problem?
N = z3.Int('N')
hard_version = constraints + [N >= 0, array_sum(N) > 0]
precond = z3.And(hard_version)
postcond = z3.Exists(i, array[i] > 0)

# This one doesn't work. (At least not within a few minutes.)
# prove(z3.Implies(precond, post

"""
***** where we ended for Feb 19 *****

===== Z3 troubleshooting =====
(we'll cover this next time)

AKA: What to do when Z3 gets stuck?

Recall that in the regex lecture, we saw that Z3 had trouble with proving one regex
constraint implies another!
"""

# Regex example from earlier
# (This won't run here, we would need to import from part 2)
# assert prove(z3.Implies(
#     z3.And(
#       z3.InRe(name, full_name_regex),
#       z3.Length(name) <= 50
#       # if you had other string variables, add more constraints here
#     ),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

# (You will need this on HW3 problem 11!)

"""
What do we do if Z3 is having trouble with a problem?

1. Bound the variables

2. Add/modify the constraints
- bounds on the variables are one form of this!
- strengthen the precondition
- relax the postcondition to something weaker
- add lemmas!

    z3.Implies(precond, hard_postcondition)
    Z3 hangs :(

    Split my problem up into two steps:
    z3.Implies(precond, lemma)
    z3.Implies(z3.And(precond, lemma), hard_postcondition)

Ask Z3 to prove each of the two statements separately!

To draw an analogy with Hypothesis: it's like putting
assert() statements earlier on in your program.

3. Use a different encoding
- use Bool, Int, Real instead of more complex types
- avoid Array, Functions

Example: we already saw an example of this
- Pigeonhole principle on HW2 part 3!

4. Do some enumeration or search outside of Z3,
     for example using itertools.

Example: HW2 part 2

    one could use Python itertools is a way of conveniently enumerating all
    permutations (reorderings) of a list.

=====

Recall:
Q: when does Z3 know to return unknown rather than hang?

A: Z3 tries to identify if it sees a case where it knows it
    beyond the capabilities of its automated decision procedures.

    EXAMPLE:
    one of the cases that Z3 solves very efficiently is if
    using Int and all your constraints are what's called linear constraints:
    a + b + c > 3 * d - e + 4 * f
    No two variables are multiplied
    Z3 has a specific built-in technique that knows how to very efficiently
    solve all linear constraints.

If your constraint doesn't lie in one of the known solvable sets,
apply one of our four techniques above for what to try
when getting stuck.
"""
