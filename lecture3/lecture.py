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

=== Day 17 ===

Last day of Z3!

Announcements:

- HW3 due Monday

- It's not too late to fill out the mid-quarter survey for 1 point of
  extra credit!
  https://forms.gle/x4z5mtJCU51X2qBb6

  You need to fill out the second form (link provided if you finish
  the survey) to get credit!
  I will close the forms at EOD Monday.

Questions about HW3?

Plan:

- Start with the poll

- Finish Z3: techniques, internals, Z3 review

===== Poll =====

Oh no, Z3 is hanging! What are some things to try?

https://forms.gle/stE1qUhWKY7yrZdn7
https://tinyurl.com/mr2frdvd

===== Z3 techniques =====

Recall that on Monday, we saw that Z3 had trouble with proving one regex
constraint implies another!
"""

# Regex example from earlier

assert prove(z3.Implies(
    z3.And(
      z3.InRe(name, full_name_regex),
      z3.Length(name) <= 50
      # if you had other string variables, add more constraints here
    ),
    z3.InRe(name, full_name_regex_generalized),
)) == PROVED

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

Example: we saw this on HW2 part 2

Python itertools is a way of conveniently enumerating all
permutations (reorderings) of a list.

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
  This should be reimiscent of solve()!

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
constraints.append(array_sum(5) > 0)
precond = z3.And(constraints)
postcond = z3.Exists(i, array[i] > 0)

# Prove
prove(z3.Implies(precond, postcond))
# This one works.

# Harder version of the problem?
# N = z3.Int('N')
# constraints.append(N >= 0)
# constraints.append(array_sum(N) > 0)
# This one doesn't work.

"""
If it didn't work?

Q: when does Z3 know to return unknown rather than hang?

A: Z3 tries to identify if it sees a case where it knows it
   beyond the capabilities of its automated decision procedures.

  Ex: one of the cases that Z3 solves very efficiently is if
  using Int and all your constraints are what's called linear constraints:
  a + b + c > 3 * d - e + 4 * f
  No two variables are multiplied
  Z3 has a specific built-in technique that knows how to very efficiently
  solve all linear constraints.

Apply one of our four techniques above for what to try
when getting stuck.

===== Z3 internals =====

So how does Z3 work anyway?
Z3 is known as an "SMT solver": Satisfiability Modulo Theories.

- We know what "satisfiability" means

  We saw this in a previous lecture

Example:
Boolean satisfiability:

(p or q or r) and (~p or ~q or ~s) and (s)

We said it's "satisfiable" if there exists some values of the input
variables such that the formula is true.

The traditional problem of satisfiability, or SAT, is with boolean
variables -- if you've taken a CS theory class, you may have seen
that this is a famous example of an NP-hard problem. What that maens
is roughly that it's impossible to solve efficiently in general, in
general you would need exponential time to solve the problem.

A traditional Satisfiability solver (SAT solver) just deals with boolean
variables. So the second part is:

- The "theories" part is the fact that it can handle different data types:
  each data type, like integers, Reals, and Strings, comes with its own
  *theory* of how to process constraints on that data type.

Example:
  x = z3.Int("x")
  x < 2 and x > 2

We have the exact same thing as before, but we've replaced
p, q, r, and s with facts about our integer data type:
"x < 2" and "x > 2" are the new p, q, r, s:
Z3 will assign boolean variables:

  p = "x < 2"
  q = "x > 2"

Then it will apply a solver for boolean satisfiability.

How do we solve boolean satisfiability?

  (p or q or r) and (~p or ~q or ~s) and (s)

Simplest idea: try values of the variables.
First try p = True, then try p = False.

But that's not very clever.
Anything we could do better?
- Suggestion to: look at s!
- s has to be true! So let's just plug in s = True.

  (p or q or r) and (~p or ~q or False) and (True)

simplifies to:
  (p or q or r) and (~p or ~q)

What else should we look at?
- Suggestion 2: look at r!
- Just pick r = True, because if it's satisfiable, it might
  as well be satisfiable with r = True.

  (p or q or True) and (~p or ~q)
  True and (~p or ~q)
  ~p or ~q

Repeat.
--> set p to False
  True or ~q
  True
and we're done. Return satisfiable.

That's the rough idea behind basic satisfiability solving (SAT)

Remember that Z3 works with arbitrary data types.
There's one last step! Write out what we have:
  s = True
  r = True
  p = False
And we use a theory-specific solver to determine
whether these are a satisfiable set of formulas for the particular
data type we are using such as z3.Int.
E.g.: if
  s = x > 0
  r = x < 0
then we would find that this is not satisfiable, and we have to go
back and try again.

Discussion:
we just solved boolean satisfiability, suppoesdly an NP-complete
problem, extremely efficiently!
How is that possible?

The entire philosophy behind Z3: satisfiability is only NP complete
in the **worst case.**
In average cases, or practical examples that come up in the real world,
it's probably not too computationally difficult to solve them.

(Not on the exam)

There are two algorithms,
we will not go over them in detail:
- DPLL: Davis-Putnam-Logemann-Loveland
  https://en.wikipedia.org/wiki/DPLL_algorithm
  That's the one that we just showed above

- CDCL: Conflict-Driven Clause Learning
  https://en.wikipedia.org/wiki/Conflict-driven_clause_learning
  Optimized/better version

===== Z3 Review =====

Proofs and satisfiability

We saw that:
Using the problem of satisfiability, we can:
- solve() constraints
- and we can prove() specifications.

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

- It can find a bug, but it can never prove that there are no bugs!

Main limitations of Z3?
(There are two)

1. We have to rewrite the program in Z3
2. Z3 might hang or return unknown

And that's where we are going next!

With general program verification frameworks!

The program and the proof will both be written in the same
framework.

===== Mid quarter review =====

This concludes the first half of the course!
See the file `mid_quarter_review.md`.
"""
