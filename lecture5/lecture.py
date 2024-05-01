"""
Lecture 5: Advanced Z3
ECS 189C
May 1, 2024
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
Complex data types

We've seen the following data types in Z3:
- Int
- Real
- Bool

Z3 has many more complex data types and operations!
- Strings
- Arrays
- Sets
- Fixed-width integers (BitVec)

Z3 also has many operations on these data types.
Remember how with integers, <, +, == etc. have to be overloaded as
operations on Z3 variables?
We do the same thing with these complex data types.

Q: why do we need all these data types and operations?

A:

Security reasons:

String data is a HUGE source of security vulnerabilities.
Top 5 web application vulnerabilities:
- Cross-site scripting (XSS):
  https://owasp.org/www-community/attacks/xss/
- Injection attacks:
  https://owasp.org/www-community/Injection_Flaws

String length issues are also a common problem:
- Hearbleed: https://xkcd.com/1354/
"""

"""
Z3 Strings

- z3.String
- z3.Length

Q: define a name that has at least 10 letters
"""

# What does z3.Length return here?

"""
- z3.StringVal
- +

Q: define a message for Hello, name!
"""

"""
Constraints between multiple strings

Q: Define strings s1, s2 such that
s1 is three copies of s2.
"""

"""
XSS example
"""

# query = z3.String("query")
# query_html = (
#     z3.StringVal("<title>Search results for:") + query + z3.StringVal("</title>")
# )

# start = z3.String("start")
# malicious_query = z3.StringVal("<script>alert('Evil XSS Script')</script>")
# end = z3.String("end")

# html = z3.String("html")

# xss_attack = z3.And(
#     html == query_html,
#     html == start + malicious_query + end
# )

# z3.solve(xss_attack)

"""
More string operations

Length, +, and == are useful, but quite limited.
For example, our "name" variable could come back with a string like

    $5$%) fdsdf 180 4

What if we want to say the string only contains the letters a-z and A-Z?
We have no way using just +, ==, and Length to do this.

Answer: regular expressions!

===== Regular expressions =====

Help notes: regex_help.md

Q: define a name that has at least 10 letters and only contains a-z and A-Z.
"""

"""
Q: only the first letter of the name should be capitalized.
"""

"""
CSV example from HW1
"""


"""
========================================
========================================
========================================
========================================
========================================
========================================
========================================
========================================
========================================
========================================

Z3 REVIEW:
Proofs and satisfiability

We should now be comfortable with using Z3 to set up a problem:
1. Declare variables
2. Declare constraints
3. Ask Z3 to solve the constraints

Z3 has two "modes" that we have used: solve() and prove().
- solve(): find a solution for *at least one* input
- prove(): prove that the statement is true *for all* inputs

How do program specifications relate to Z3?
(Problem 1B on HW2 is about this)

    inputs = ... # Z3 variables
    output = call_program(inputs)
    precondition = ...
    postcondition = ...
    spec = z3.Implies(precondition, postcondition)
    prove(spec)

We can also use Z3 more like Hypothesis to generate example inputs.
How?

    inputs = ... # Z3 variables
    precondition = ...
    example = get_solution(precondition)

^^ This is basically how Hypothesis works!

We saw that the main limitation of Hypothesis was?

Main limitation of Z3?
"""
