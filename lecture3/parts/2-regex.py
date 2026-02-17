"""
ECS 189C Lecture 3

Part 2: Regular expressions
"""

import z3
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

"""
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

  (if you're familiar with regex from a theoretical CS class - s ∈ L(R))

The string "matches" the regex R if the pattern is present/true,
and does not match if it's not present/false.

Q: define a name that has at least 10 letters and only contains a-z.

In a theoretical CS context, regex are using characters, union, concatenation, and star

In Z3, we have all of thes operations, as well as several others to support practical regex
constructs.
(Same is true in other regex libraries for popular programming languages.)

"""

# What we had before...
name = z3.String("name")
length_constraint = z3.Length(name) >= 10

# Our regex constraint...
# z3.Range
lowercase_letter = z3.Range("a", "z")
                  # ^^^^^^^^^^^^^^^^ Range Regex
                  # matches a single character 'between' lowercase a and lowercase z
                  # (in ASCII code.)
                  # Inclusive range
                  # Includes both the start and the end.

"""
matches? "x" "y" "a" "b" "r" --> a single character that is a lowercase letter
doesn't match? "" "cat" "ASDFBDF" "$"
"""

# z3.Star -- indicates repetition of the same pattern. It matches
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
# most important regex operator!!
regex_constraint = z3.InRe(name, lowercase_letters)

# Now let's solve our constraint
z3.solve(z3.And(
  length_constraint,
  regex_constraint,
))

# Now our name is pppppppppp!

# Hooray, no capital letters!

# We can go from there to make the constraint more realistic...
# - First letter should be capital
# - The name contains vowels
# - ...

"""
Today we covered: Strings part of the lecture,
and started to see how to use regex to define more interesting/complicated constraints
on general strings.
We will see that this is very useful for writing Z3 applications which solve or prove
for specifications involving strings using the Z3 string datatype,
and will be used on HW3.

----- Where we ended for today -----

=== Exercise ===

Define a string 'name' such that only the first letter is capitalized.
"""

# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .
# .

# capital_letter = z3.Range("A", "Z")

# # We already have our lowercase character regex... so let's combine them!
# # How do we combine two regex constraints?
# # If you want pattern1 **followed by** pattern 2, we use
# # z3.Concat

# name_regex = z3.Concat(capital_letter, lowercase_letters)
# regex_constraint = z3.InRe(name, name_regex)

# z3.solve(z3.And(
#   length_constraint,
#   regex_constraint,
# ))

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

# # Let's reuse what we already have!
# # How do we convert " " to a Regex (from a Python string)?
# # We could use z3.Range, but there's a simpler way
# # Let's refer to regex_help.md
# # We can use z3.Re
# full_name_regex = z3.Concat(
#   name_regex,
#   z3.Re(" "),
#   name_regex,
# )

# solve(z3.And(
#   length_constraint,
#   z3.InRe(name, full_name_regex),
# ))

# # Middle names?
# # We could do one for 3 names, one for 2 names,
# # and z3.Or them
# # Let's actually use z3.Union: basically OR for regexes

# full_name_regex = z3.Concat(
#   # Firstname
#   name_regex,
#   z3.Re(" "),
#   # Middlename
#   z3.Union(
#     z3.Re(""),
#     z3.Concat(name_regex, z3.Re(" "))
#   ),
#   # Lastname
#   name_regex,
# )

# solve(z3.And(
#   length_constraint,
#   z3.InRe(name, full_name_regex),
# ))

# # What if we want to allow more than just 3 names?
# # (Real names can have any number of parts)
# # Use z3.Star?
# # Generalization of z3.Concat for any number
# # of parts.

# full_name_regex_generalized = z3.Concat(
#   # Firstname
#   name_regex,
#   z3.Star(
#     # Any further names here (Middle name, last name, etc.)
#     z3.Concat(z3.Re(" "), name_regex)
#   ),
# )

# solve(z3.And(
#   length_constraint,
#   z3.InRe(name, full_name_regex),
# ))

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

# from helper import prove, PROVED

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

# assert prove(z3.Implies(
#     z3.And(
#       z3.InRe(name, full_name_regex),
#       z3.Length(name) <= 20
#     ),
#     z3.InRe(name, full_name_regex_generalized),
# )) == PROVED

"""
===== Poll/Exercise =====

What regex operators would be useful to write a Z3 regex to match US phone numbers?
  555-555-5555

"""

# phone_number = z3.String("phone_number")
# number = z3.Range("0","9")
# hyphen = z3.Re("-")

# length_constraint = z3.Length(phone_number) >= 12

# # Start to concatenate them!
# regex_constraint = z3.Concat(
#   number,
#   number,
#   number,
#   hyphen,
#   number,
#   number,
#   number,
#   hyphen,
#   number,
#   number,
#   number,
#   number,
# )

# z3.solve(z3.InRe(phone_number, regex_constraint))

# # Four numbers?
# z3.Concat(number, number, number, number)

# last_part = z3.String("last_part")
# z3.And(
#   z3.Length(last_part) == 4,
#   z3.InRe(last_part, z3.Star(number))
# )

# # Would also have to use string concatenation like...
# # phone_number = first_part + "-" + second_part + "-" + last_part

# # What is star? 0 or more repetitions.
# # "" or number or number, number or number, number, number or
# #      number, number, number, number, ....

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

# n = z3.Int("n")
# s = z3.String("n_to_string")
# spec = z3.And(
#   n >= 123,
#   s == z3.IntToStr(n),
# )
# solve(spec)

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

# not_empty = z3.String("s")
# regex_constraint = z3.Complement(z3.Re(""))

# solve(z3.InRe(not_empty, regex_constraint))

# We could have also done this with z3.Length(s) >= 1.

"""
=== CSV example from HW1 ===

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
=== Recap: Part 3 ===

- Showed some of the remaining Z3 regex operators
- Encourage to read regex_help.md as you're using Z3 regex, in
  addition to the lecture material to remind yourself about
  what each regex constructor does.
- Advanced data types: Functions and Arrays.
"""
