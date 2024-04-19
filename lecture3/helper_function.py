"""
Helper functions

These helper functions can be useful when working with Z3.
The main difference between z3.prove and
z3.solve is that they also return the result.

These will be available for you to use on the homework.

So for example you can do
result = solve(spec)
assert result == z3.sat

to assert that a formula `spec` is satisfiable.
"""

def prove(spec):
    solver = z3.Solver()
    solver.add(z3.Not(spec))
    result = solver.check()
    if result == z3.unsat:
        print("proved")
    elif result == z3.unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())
    return result

def solve(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == z3.unsat:
        print("no solution")
    elif result == z3.unknown:
        print("failed to solve")
    else:
        print("solution found")
        print(s.model())
    return result
