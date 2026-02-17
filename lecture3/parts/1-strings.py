"""
ECS 189C: Lecture 3

Part 1: Z3 Strings

Plan for all of lecture 3:

- Strings and regular expressions in Z3
- Z3 internals
- Advanced Z3 techniques
- Z3 review

Questions?

===== Intro =====

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

A: We need these data types to be able to model real programs,
since real programs use strings, arrays, fixed-width integers,
etc.

Security reasons:

String data is a HUGE source of security vulnerabilities.
Top 5 web application vulnerabilities:
- Cross-site scripting (XSS):
  https://owasp.org/www-community/attacks/xss/
- Injection attacks:
  https://owasp.org/www-community/Injection_Flaws

String length issues are also a common problem:
- Heartbleed: https://xkcd.com/1354/

===== Z3 Strings =====

What is a string?
- An array of chars.
What are characters?
ASCII characters? == bytes
In Z3: Characters == Unicode chars
So we will think of strings as:
- A sequence of unicode chars
- We don't care how the sequence is encoded.

- z3.String
- z3.Length

Q: define a name that has at least 10 letters
"""

import z3
import pytest
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

name = z3.String("name")
constraint = z3.Length(name) >= 10
solve(constraint)

# Comment: In this case it returned ASCII!
# But, if you play around you will quickly encounter cases
# where it returns strange unicode code points, and they
# might even display weirdly on your terminal as things like
#  \u{32} \u{50}

# Often, it's useful to just assume the whole string is ASCII,
# and we will see how to do that in a few minutes.

# Q: What does z3.Length return here?
# A: It's a Z3 integer.
# Fortunately, we already know how to work with integers!
# So you can do any operation you're familiar with on integers,
# on the string length.

"""
- z3.StringVal
- +

Similar for integers: there's Int and there's IntVal.
An IntVal is just a specific (constant) integer.
Similarly, a StringVal is a specific (constant) string like
"Hello" or "Cats and dogs".

Q: define a message for Hello, name!
"""

msg = z3.String("msg")
name_constraint = z3.Length(name) >= 10
# msg_constraint = (msg == z3.StringVal("Hello, ") + name + z3.StringVal("!"))
msg_constraint = (msg == "Hello, " + name + "!")

solve(z3.And(name_constraint, msg_constraint))

# Basically, StringVal converts a Python string into a Z3 string.
# With integers and Booleans, we didn't use this too often, because
# it was happening automatically behind the scenes.

# Can we omit the StringVal?
# Yes! Z3 automatically converts a Python string into a Z3 StringVal in this case.

"""
Constraints between multiple strings

Q: Define strings s1, s2 such that
s1 is three copies of s2
and s2 is not empty
"""

s1 = z3.String("s1")
s2 = z3.String("s2")
constraints = [
  s1 == s2 + s2 + s2,
  s2 != "",
  s2 != "A",
  s2 != "B",
  z3.Length(s2) >= 2,
]
solve(z3.And(constraints))

"""
XSS example

Use Z3 to show that a cross site scripting (XSS) attack is possible
for an example HTML page.

(Very minimized example)

What is an XSS attack?
Basically, an XSS attack is where we insert a malicious script
to be executed on a page which was not intended to execute the
script.
"""

query = z3.String("query")
query_html = (
    z3.StringVal("<title>Search results for:") + query + z3.StringVal("</title>")
)

start = z3.String("start")
malicious_query = z3.StringVal("<script>alert('Evil XSS Script')</script>")
end = z3.String("end")

# Make a variable for the entire contents of the HTML page.
html = z3.String("html")

xss_attack = z3.And(
    html == query_html,
    html == start + malicious_query + end
)

z3.solve(xss_attack)

"""
Recap:
- We looked at the string data type in Z3
- We saw simple string operations (+, ==, Length)
- We saw a suggestive example of using strings to detect the possibility
  of a security attack (XSS attack).
- To define more complciated constraints on strings, one almost always
  needs to use regexes, using z3.InRe. That is where we will go next.
"""
