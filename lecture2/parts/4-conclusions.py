"""
ECS 189C
Lecture 2, Part 5:

Conclusions
"""

import z3
from helper import solve, prove

"""
=== True Real Numbers ===

We've seen so far how Z3 can work with standard Python datatypes.

Because Z3 is a theorem prover, and not just a testing framework,
it can also work with data types that are not available in Python:
for example, real numbers.

In Python, there's no such thing as a "true" real number,
there are only floating point values (floats)
But in Z3 there is.

z3.Real
z3.Reals
"""

# x = z3.Real('x')
# # what happens?
# print("Square root of two:")
# z3.solve(x * x == 2)

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

"""
More advanced data types:
(later)
- Functions
- Arrays and sequences
- Strings and regular expressions
"""

"""
Exercises

Q: Write a function to determine whether a number
is a perfect square, first as an integer, then as a real number.

Q: write a function to solve the formula
x^2 + 5x + 6 = 0

First as an integer, then as a real number.
"""

"""
=== Conclusions and summary points ===

Three-step methodology (thinking about problems / Z3 mindset):



Satisfiability vs. Proof:




Advantages/disadvantages of using Z3 for proving specs of real programs?




=== Other tips and resources ===

Useful guide:
[Z3 py guide](https://ericpony.github.io/z3py-tutorial/guide-examples.htm)

Documentation:
[Z3 py docs](https://z3prover.github.io/api/html/namespacez3py.html)

The Z3 solver API:
see helper.py.

Useful on the HW.
"""
