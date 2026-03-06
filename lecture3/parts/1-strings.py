"""
ECS 189C: Lecture 3

Part 1: Z3 Strings

Plan for all of lecture 3:

- Strings and regular expressions in Z3
- Z3 internals
- Advanced Z3 techniques
- Z3 review

===== Intro =====

Complex data types

We've seen the following data types in Z3:
- Int
- Bool
- Real

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

=== Poll ===

Q: Why might we need complex data types and operations in Z3?

https://forms.gle/arvFeDGcdBAoHDRp9

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
.
.
.
.
.

A1:
In order to model real programs - since real programs use strings, arrays,
fixed-width integers, etc.

A2:
Practical applications

E.g.: Security

    String data is a HUGE source of security vulnerabilities.

    Top 5 web application vulnerabilities (OWASP):
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

    ^^^^ outdated answer
    (CStrings - C string is typicall a sequence of bytes)

    Good enough for a-z, 0-9, special characters
    but not more general characters (outside of latin alphabet, emojis)

Today, most often:

    Characters = Unicode chars

    But - still a sequence of chars

This is also the approach that Z3 will take
So we will think of strings as:

- A sequence of unicode chars
- We don't care how the sequence is encoded.

- z3.String
- z3.Length

Q: define a name that has at least 10 letters
"""

import z3
from helper import solve, get_solution, SAT, UNSAT, UNKNOWN

def name_ex_1():
    name = z3.String("name")
    constraint = z3.Length(name) >= 10
    solve(constraint)

# Uncomment to run
# name_ex_1()

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

# name - String var (a String expression)
# z3.Length(name) - Integer expression
# constraint - Boolean expression

"""
- z3.StringVal
- +

Similar for integers: there's Int and there's IntVal.
An IntVal is just a specific (constant) integer.
Similarly, a StringVal is a specific (constant) string like
"Hello" or "Cats and dogs".

    IntVal - cast a Python integer into Z3 integer expression

    StringVal - cast a Python string into a Z3 string

        i.e. a string literal.

Q: define a message for Hello, name!
"""

def name_ex_2():
    name = z3.String("name")
    msg = z3.String("msg")
    name_constraint = z3.Length(name) >= 10
    # name_constraint = z3.Or(name == "Alice", name == "Bob", name == "Charlie")
    # msg_constraint = (msg == z3.StringVal("Hello, ") + name + z3.StringVal("!"))
    msg_constraint = (msg == "Hello, " + name + "!")

    solve(z3.And(name_constraint, msg_constraint))

# Uncomment to run
# name_ex_2()

# Basically, StringVal converts a Python string into a Z3 string.
# With integers and Booleans, we didn't use this too often, because
# it was happening automatically behind the scenes.

# Can we omit the StringVal?
# Yes! Z3 automatically converts a Python string into a Z3 StringVal in this case.

"""
Constraints between multiple strings

Q: Define strings s1, s2 such that
s1 is three copies of s2
and s2 is not empty, s2 is at least 2 characters
"""

def concat_ex():
    s1 = z3.String("s1")
    s2 = z3.String("s2")
    constraints = [
        s1 == s2 + s2 + s2,
        # Add more constraints to make the example more interesting...
        s2 != "",
        s2 != "A",
        s2 != "B",

        z3.Length(s2) >= 2,
    ]
    solve(z3.And(constraints))

# Uncomment to run
# concat_ex()

"""
Other constraints?

String not containing A or B?

- make some variables for prefix and suffix
- s2 != prefix + "A" + suffix
"""

# s1 = z3.String("s1")
# s2 = z3.String("s2")
# prefix = z3.String("prefix")
# suffix = z3.String("suffix")
# constraints = [
#     s1 == s2 + s2 + s2,
#     s2 != prefix + "A" + suffix,
#     # s2 == "CAT",
#     z3.Length(s2) >= 2
# ]
# solve(z3.And(constraints))

"""
what happened?

- we wanted to say that S2 should not be equal to prefix + "A" + suffix for **all* prefixes/suffixes

- but we actually said that it's not equal to prefix + "A" + suffix only for some particular prefix/suffix
    (which is useless).

We can solve this in multiple ways, using some of the techniques next.

It does look like we need a way to say "string s2 contains string s3"

    z3.Contains

also can do with:

    z3.ForAll([prefix, suffix], s2 != prefix + "A" + suffix),

Easiest solution in this case:

    We need a new string operation! (can't do with existing ones)

    z3.Contains is the operation we're looking for

    More generally - we'll see that a much more expressive set of operations
    is available to us using regular expressions in part 2.

=====

XSS example

Use Z3 to show that a cross site scripting (XSS) attack is possible
for an example HTML page.

(Very minimized/toy example)

What is an XSS attack?
Basically, an XSS attack is where we insert a malicious script
to be executed on a page which was not intended to execute the
script.
"""

def xss_example():
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

    # TODO:
    # To make example more convincing,
    # Encode the constraint that the website consists of separately matched <title> and </title>
    # and <script> / </script> tags.

# Uncomment to run
# xss_example()

"""
Exercise:
(Skip for now)

Define a Z3 constraint to solve for a website URL
that contains google.com, but where the domain name is not "google"
"""

"""
More string operations?

Length, +, and == are useful, but quite limited.

Another example of how they are limited:
    our "name" variable could come back with a string like

    $5$%) fdsdf 180 4

    (or something even worse with unicode code points)

- What if we want to say the string only contains the letters a-z and A-Z?

- What if we want to say that the string should NOT contain the letters a-z and A-Z?

We have no way using just +, ==, and Length to do this.

Answer: regular expressions!
"""

"""
Recap:
- We looked at the string data type in Z3
- We saw simple string operations (+, ==, Length)
- We played around with using these to define constraints on strings -
    but saw that it was hard to encode certain constraints, such as
    "string s2 contains an A"
- We saw a suggestive example of using strings to detect the possibility
  of a security attack (XSS attack).
- To define more complicated constraints on strings, one almost always
  needs to use regexes, using z3.InRe. That is where we will go next.
"""
