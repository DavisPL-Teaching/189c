"""
This example was from lecture 3
"""

import z3

def absolute_value_z3(x):
    return z3.If(x < 0, -x, x)

# Notice this is exactly the same function as before,
# but written in a different way, now with z3.If.

def test_absolute_value_z3():
    x = z3.Int('x')
    y = absolute_value_z3(x)
    spec = z3.And(z3.Or(y == x, y == -x), y >= 0)
    z3.prove(spec)

test_absolute_value_z3()
