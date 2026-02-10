"""
ECS 189C
Lecture 2, Part 4:

Conclusion & End Notes

=== Poll ===

(A bit of foreshadowing)

Which of the following is a reason Z3 might return "Unknown"?

A. Use of a large number of Boolean and Integer variables
B. Use of strings and regular expressions
C. Use of functions and arrays
D. Use of advanced quantifiers: z3.ForAll and z3.Exists
E. Encoding a mathematically complex property, like an advanced mathematical theorem (e.g., Fermat's Last Theorem)

https://forms.gle/BwpKaqL67EiE3sNm6
"""

import z3
from helper import solve, prove

"""
A few remaining things to mention...

=== Failing to solve a problem: Returning unknown or hanging ===

We have seen that Z3 can return UNKNOWN as a cop-out option -
it basically means "I don't know".

Z3 will return unknown if it *knows* it can't solve the problem.
So are there cases Z3 fails, but does not return unknown?

Yes - see HW.
Example from my own testing last year:

- https://pastebin.com/D1cX6egj

Another example:

- https://github.com/cdstanford/curiosities/blob/master/chess-moves/chess-moves.py

Q: what difference can we infer from cases hanging vs. returning unknown?

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

A: both cases are common for mathematically complex formulas.
However the following is the distinction:

- If the formula uses some form/construct that Z3 *knows* it can't handle,
  it will return UNKNOWN

- If the formula looks solvable (e.g., only integers and Booleans), but
  just takes a long time to solve or doesn't go anywhere, Z3 will hang
  or return an answer very slowly.

.
.
.

A few other things...

=== True Real Numbers ===

We've seen so far how Z3 can work with standard Python datatypes.

Because Z3 is a theorem prover, and not just a testing framework,
it can also work with data types that are not available in Python:
for example, real numbers.

In Python, there's no such thing as a "true" real number,
there are only floating point values (floats)
But in Z3 there is.

z3.Real
"""

# x = z3.Real('x')
# y = z3.Real('y')
# # what happens?
# print("Square root of two:")
# solve(z3.And(x * x == 2, x > 0, y == 1000000 * x))

# Note: there is no floating point value x with x^2 = 2
# It only exists as a true real number.

# How does Z3 represent real numbers, when computers can't
# represent real numbers?

# Answer: they're treated as abstract symbols, not as concrete
# values.
# In fact, everything in Z3 is treated as abstract symbols!
# z3.If, z3.Int, z3.Or, the reason there's a Z3 version is that
# it treats it as an abstract formula, not a concrete value.
# Just like when I write x = sqrt(2) on the board, I'm not actually
# computing the exact value of x, that's the same thing that Z3
# does.

# x = z3.Int('x')
# # what happens?
# print("Square root of two:")
# solve(z3.And(x * x == 2, x > 0))

"""
Exercises

Q: Write a function to determine whether a number
is a perfect square, first as an integer, then as a real number.

Q: write a function to solve the formula
x^2 + 5x + 6 = 0

First as an integer, then as a real number.
"""

"""
=== Advanced Z3 ===

One thing missing from our discussion of Z3
is more advanced data types.
Z3 supports many, for example:

- Functions
- Arrays and sequences
- Strings and regular expressions

We will discuss some of these in Lecture 3.
However, there is a risk!
Usually, working with advanced data types (especially, functions & arrays) makes Z3 more
likely to return unknown.
You saw an example of this on the HW2, part 3.

Sticking with Booleans, Ints is usually better for Z3 to terminate successfully.
(Strings and regular expressions is also usually OK).

=== Recap and limitations of Z3? ===

We have seen Z3! main advantages?

- We can prove the spec on ALL inputs

- We can solve systems of constraints - without coding some
  logic for how to find the solution, we instead treat
  it as a "magic box" that gives us the answer

Main disadvantages (there are two):

1. We have to rewrite the program in Z3

2. Z3 might hang or return unknown.

"""

"""

=== Summary points ===

Three-step methodology (thinking about problems / Z3 mindset):

1. Define your variables
2. Define your constraints
3. Call solve/prove

Satisfiability:

    A formula is satisfiable if there exists at least one input
    such that the formula is true

Solve() vs. prove()

    z3.prove(spec) equiv to z3.solve(not(spec))

Applications of Z3:
useful for logic programming & constraint solving.
Given any problem that can be solved by defining a system of constraints
(Sudoku, trailer puzzle, 8 queens, traveling salesperson, etc.)
There are many other applications.

=== Other tips and resources ===

Useful guide:
[Z3 py guide](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

Documentation:
[Z3 py docs](https://z3prover.github.io/api/html/namespacez3py.html)

The Z3 solver API:
see helper.py.

Useful to have these open when working with Z3!
"""
