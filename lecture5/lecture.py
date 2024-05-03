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

########## Where we left off for Day 13 ##########

=== Day 14 ===

To follow along: we're in lecture5/lecture.py

- HW2 due today!
- HW3 due in 1 week

Plan: Finish up Z3 either today or today + next time

- Strings and regular expressions in Z3
- Advanced Z3 techniques
- Z3 review

Questions?

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
More string operations

Length, +, and == are useful, but quite limited.

For example, our "name" variable could come back with a string like

    $5$%) fdsdf 180 4

- What if we want to say the string only contains the letters a-z and A-Z?

- What if we want to say that the string should NOT contain the letters a-z and A-Z?

We have no way using just +, ==, and Length to do this.

Answer: regular expressions!

===== Regular expressions =====

Help notes: regex_help.md

What is a regular expression?
A "pattern" that a string may or may not satisfy.
-> you can think of it as a boolean on strings.
For example:
- the string contains the word "cat" inside it
- the string is only ASCII characters
- the string has no capital letters
- ...
Roughly:
a pattern of characters that is or is not present in the string.

Most important thing: if you have a string s and a regular expression
(or regex, for short) R, you can ask

  Does s match R?

The string "matches" the regex R if the pattern is present/true,
and does not match if it's not present/false.

Q: define a name that has at least 10 letters and only contains a-z.
"""

# What we had before...
name = z3.String("name")
length_constraint = z3.Length(name) >= 10

# Our regex constraint...
# z3.Range
lowercase_letter = z3.Range("a", "z")
"""
matches? "x" "y" "a" "b" "r" --> a single character that is a lowercase letter
doesn't match? "" "cat" "ASDFBDF" "$"
"""
# z3.Star -- kind of like a for loop, it matches
# the same thing zero or more times.
lowercase_letters = z3.Star(lowercase_letter)
"""
matches? "" "cat" "dog" "xyz" "thequickbrownfoxjumpedoverthelazydogs" etc.
doesn't match? "c a t" "$$$" "asdfkl;ajsdg4" etc.
"""
# Last thing we need?
# Turn the regex into a constraint on the string.
# We use the fundamental operation of regexes! Does a string s match
# a regex R?
# In Z3, the operation for this is z3.InRe
regex_constraint = z3.InRe(name, lowercase_letters)

# Now let's solve our constraint
z3.solve(z3.And(
  length_constraint,
  regex_constraint,
))
# Now our name is dcapphpppp!
# Hooray, no capital letters!

"""
Recap:
- We looked at the string data type in Z3
- We saw simple string operations (+, ==, Length)
- We saw a suggestive example of using strings to detect the possibility
  of a security attack (XSS attack).
- Do define more complciated constraints on strings, one almost always
  needs to use regexes, using z3.InRe, and we saw a few of the
  regex constructors.
"""

############# Where we left off for day 14

"""
Q: only the first letter of the name should be capitalized.
"""

"""
Q: what if we want to allow spaces?
"""

"""
CSV example from HW1
"""

"""
===== Other data types =====

(Very brief)
Some of the other most useful types:
- Z3 arrays
- Z3 functions
"""

# Function example
# x = Int('x')
# y = Int('y')
# f = Function('f', IntSort(), IntSort())
# solve(f(f(x)) == x, f(x) == y, x != y)

# Array example

# A = Array('A', I, I)
# x = Int('x')

"""
You can even create your own datatypes:
"""

# TreeList = Datatype('TreeList')
# Tree     = Datatype('Tree')
# Tree.declare('leaf', ('val', IntSort()))
# Tree.declare('node', ('left', TreeList), ('right', TreeList))
# TreeList.declare('nil')
# TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))

# Tree, TreeList = CreateDatatypes(Tree, TreeList)

"""
===== Poll =====

What are some reasons that Z3 might return UNKNOWN?

https://forms.gle/Af8sYHsSmenHU6it6
https://tinyurl.com/5fe9k3ee

===== Z3 techniques =====

What do we do if Z3 is having trouble with a problem?

1. Bound the variables

2. Add additional constraints

3. Use a different encoding
- use Bool, Int, Float instead of more complex types
- avoid Array, Functions

Example: Sudoku
"""

# Array example
# We want an array with 3 elements.
# 1. Bad solution
# X = Array('x', IntSort(), IntSort())
# # Example using the array
# print (X[0] + X[1] + X[2] >=0)

# 2. More efficient solution

"""
===== Z3 Review =====

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

Main limitations of Z3?
"""
