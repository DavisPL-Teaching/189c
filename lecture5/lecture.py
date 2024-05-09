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
=== Day 15 ===

Announcements:

- Mid-quarter survey!
  https://forms.gle/x4z5mtJCU51X2qBb6

  + Counts for 1 point of extra credit

- REU application:
  https://forms.gle/VEAyBAMWWHfUwQY8A

- I will be moving the HW3 deadline to Monday (May 13)

  + I will announce this on Piazza later today

  + Future homeworks will be due on Mondays so that you
    have both Friday and Monday office hours to ask questions.

Today:

- Start with poll we didn't get to last time

- Continue with regexes in Z3

This week:

- Finish up Z3 (either today or today + next time)

- Start on Dafny

Questions?

===== Poll =====

What are some reasons that Z3 might return UNKNOWN?

https://forms.gle/Af8sYHsSmenHU6it6
https://tinyurl.com/5fe9k3ee

"""

"""
Recall:
Last class, we used Z3 regexes to define a string variable 'name'
that only contains lowercase letters. What else can we do with regexes?

Q: Define a string 'name' such that only the first letter
   is capitalized.
"""

capital_letter = z3.Range("A", "Z")

# We already have our lowercase character regex... so let's combine them!
# How do we combine two regex constraints?
# If you want pattern1 **followed by** pattern 2, we use
# z3.Concat

name_regex = z3.Concat(capital_letter, lowercase_letters)
regex_constraint = z3.InRe(name, name_regex)

z3.solve(z3.And(
  length_constraint,
  regex_constraint,
))

"""
How does Z3 regex differ from practical regexes?

Some operations present in practical regex libraries may not
be present in Z3 and will require encoding them in some way,
for example:
  - capture groups
  - anchors like ^ and $
  - case-insensitivity, where we want to automatically consider
    'a' and 'A' to be the same
  - matching any alphanumeric character

While there are more advanced solutions, the easiest way
to do these sorts of constraints is to write your own Ranges and
similar for the different characters you're interested in.
"""

"""
Q: Modify the string to allow spaces.

But: we don't spaces at the beginning or end of the string, we want
something like
  Firstname Lastname
  or
  Firstname Middle Lastname

So how can we do this?
"""

# Let's reuse what we already have!
# How do we convert " " to a Regex (from a Python string)?
# We could use z3.Range, but there's a simpler way
# Let's refer to regex_help.md
# We can use z3.Re
full_name_regex = z3.Concat(
  name_regex,
  z3.Re(" "),
  name_regex,
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# Middle names?
# We could do one for 3 names, one for 2 names,
# and z3.Or them
# Let's actually use z3.Union: basically OR for regexes

full_name_regex = z3.Concat(
  # Firstname
  name_regex,
  z3.Re(" "),
  # Middlename
  z3.Union(
    z3.Re(""),
    z3.Concat(name_regex, z3.Re(" "))
  ),
  # Lastname
  name_regex,
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# What if we want to allow more than just 3 names?
# (Real names can have any number of parts)
# Use z3.Star?
# Generalization of z3.Concat for any number
# of parts.

full_name_regex_generalized = z3.Concat(
  # Firstname
  name_regex,
  z3.Star(
    # Any further names here (Middle name, last name, etc.)
    z3.Concat(z3.Re(" "), name_regex)
  ),
)

solve(z3.And(
  length_constraint,
  z3.InRe(name, full_name_regex),
))

# Q: How do length_constraint and z3.InRe both know to
# constraint the entire string?
# A: because they both refer to the 'name' variable.

"""
Q: We know that full_name_regex_generalized
refers to a name with any number of spaces
and full_name_regex refers to a name with
exactly 2 or 3 parts.

Is full_name_regex_generalized actually more general?
In other words,
does full_name_regex **imply** full_name_regex_generalized?

(Useful for HW problem 11)

How would we do this?

Use z3.Implies! We've seen this pattern
several times:

    z3.Implies(precondition, postcondition)

To show that R2 is more general than R1,
we could show that

    precondition: s matches R1
    postcondition: s matches R2

How we write that in Z3?

    z3.Implies(z3.InRe(s, r1), z3.InRe(s, r2))
"""

from helper import prove, PROVED

# This should pass
# assert prove(z3.Implies(
#     z3.InRe(name, full_name_regex),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

# Z3 hangs! :O

# What do we do to fix this?
# Tip: bound your variables.
# Add a constraint that the string is at most, e.g.
# 25 or 100 characters.

assert prove(z3.Implies(
    z3.And(
      z3.InRe(name, full_name_regex),
      z3.Length(name) <= 20
    ),
    z3.InRe(name, full_name_regex_generalized),
)) == PROVED

########## where we left off for day 15 ##########

"""
=== Day 16 ===

- HW2 has been graded!

- Reminder: Fill out the mid-quarter survey!
  https://forms.gle/x4z5mtJCU51X2qBb6

- HW3 due Monday, OH on Friday (x2) and Monday

Plan:

- Go over a couple of problems from HW2

- Poll

- Finishing up strings and regexes

- Advanced data types + Z3 techniques

(Advanced data types will not be on final)

Questions:

===== HW2 review =====

- Part 1: rectangle collision and extra credit

- Part 2: some approaches that work, some that don't

- Style: code duplication

===== Poll =====

What regex operators would be useful to write a Z3 regex to match US phone numbers?
  555-555-5555

https://forms.gle/UQPebaxeH813LC4x7
https://tinyurl.com/yytvmk5m
"""

phone_number = z3.String("phone_number")
number = z3.Range("0","9")
hyphen = z3.Re("-")

length_constraint = z3.Length(phone_number) >= 12

# Start to concatenate them!
regex_constraint = z3.Concat(
  number,
  number,
  number,
  hyphen,
  number,
  number,
  number,
  hyphen,
  number,
  number,
  number,
  number,
)

z3.solve(z3.InRe(phone_number, regex_constraint))

# Four numbers?
z3.Concat(number, number, number, number)

last_part = z3.String("last_part")
z3.And(
  z3.Length(last_part) == 4,
  z3.InRe(last_part, z3.Star(number))
)

# Would also have to use string concatenation like...
# phone_number = first_part + "-" + second_part + "-" + last_part

# What is star? 0 or more repetitions.
# "" or number or number, number or number, number, number or
#      number, number, number, number, ....

"""
===== Finishing up strings and regexes =====

Recap: we have seen:
  Concat, Union, Star, Range, Re
and the fundamental operation
  InRe(s, R)
to assert that a string matches a regex R.

Other Regex operators we haven't seen in class (see regex_help.md):
- z3.Plus
  Like Star but one or more times, insetad of zero or more times.
- z3.IntToStr
  z3.IntToStr(9) to get the digit 9
  z3.IntToStr(n) to get the string corresponding to the Z3 int n.
- z3.CharIsDigit
"""

n = z3.Int("n")
s = z3.String("n_to_string")
spec = z3.And(
  n >= 123,
  s == z3.IntToStr(n),
)
solve(spec)

# Q: why a special operation for IntToStr? I didn't learn about this
# in my previous regex tutorial/class
# A: It's a complex operation and it's totally not obvious how to do it
# without built-in support.
# Basically, serializing a number using its base 10 representation.

"""
There are others!
Union is like OR.
What about AND and NOT? Those also have regex equivalents.

- z3.Intersect(R1, R2): a regex
  matching all strings that match both R1 and R2
- z3.Complement(R)
  matches all strings that DON'T match R.

Example:
Q: Use a regex to define a string that is NOT equal to the empty string.
"""

not_empty = z3.String("s")
regex_constraint = z3.Complement(z3.Re(""))

solve(z3.InRe(not_empty, regex_constraint))

# We could have also done this with z3.Length(s) >= 1.

"""
CSV example from HW1
(Optional or skip for time)

Recall: On HW1 part 2, you were asked to write a simple
serialization and deserialization function for a User class.
It looked like this:

def to_csv(user):
  ...

def from_csv(csv):
  ...

It was possible to show using Hypothesis that some inputs can
cause to_csv and from_csv to break.

Bug: where the user sets their name to "Hi,My,Name,Has,Commas"
  age: 50
serialization returns:
  Hi,My,Name,Has,Commas,50
deserialization gets confused!

Q: How could we use Z3 to model this scenario?

Problems to validate with Z3:
- the deserialization doesn't match the original user!
- there are 2 different deserializations for the same string!

Q: How could we use Z3 to validate our solution?

- Restrict the name to not contain commas?
- Change the deserialization function to handle commas?

Z3 could be used to prove that both of these work.
"""

"""
===== Other data types =====

(Briefly)
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
f = z3.Function('f', I, I)
constraints = [f(f(x)) == x, f(x) == y, x != y]
solve(z3.And(constraints))

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
solve(A[0] + A[1] + A[2] >=0)

# we can store things in the array
x = z3.Int('x')
print(A[x])
print(z3.Store(A, x, 10))

# Q: how is the array different from a list of integers?
# [z3.Int("x1"), z3.Int("x2"), z3.Int("x3")]
# We can only define a fixed finite number of Z3 variables this way.
# Arrays (and functions) have infinitely many possible indices
# and so can be used to model very general scenarios.

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
Recap:
- Showed some of the remaining Z3 regex operators
- Encourage to read regex_help.md as you're using Z3 regex, in
  addition to the lecture material to remind yourself about
  what each regex constructor does.
- Advanced data types: Functions and Arrays.

Next time: advanced techniques (if your code hangs or returns Unknown)
and wrap up with advantages/disadvantages of Z3 overall
to move on to the next part of the class.

===== Z3 techniques =====

Recall that last time, we saw that Z3 had trouble with proving one regex
constraint implies another!

What do we do if Z3 is having trouble with a problem?

1. Bound the variables

2. Add additional constraints

3. Use a different encoding
- use Bool, Int, Float instead of more complex types
- avoid Array, Functions

Example: Sudoku
"""

# Regex example from earlier

# assert prove(z3.Implies(
#     z3.And(
#       z3.InRe(name, full_name_regex),
#       z3.Length(name) <= 50
#     ),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

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
