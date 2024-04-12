"""
Lecture 2

git clone https://github.com/DavisPL-Teaching/189C.git
or
git pull
(If you have changes, you will want to discard them first.)
"""

from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings
from hypothesis import assume
import pytest

####################
###     Poll     ###
####################

# Here are 3 programs, and 4 specifications. For each program, which
# specification(s) does it satisfy?
# For all programs, assume that the input is an arbitrary integer.

# The decorator is generating an arbitrary integer
# @given(st.integers())

# Programs:
def p1(x):
    return x + 1
def p2(x):
    return x + x
def p3(x):
    return x * x + 1

# Specifications:
def s1(x):
    assert type(p(x)) is int
def s2(x):
    assert p(x) > x
def s3(x):
    assert p(x) == x * x
def s4(x):
    assert p(1) == 2

# FORM: https://tinyurl.com/2p79r6y6

######################
###     Part 1     ###
######################
# Writing preconditions
# + useful Hypothesis/pytest syntax

# We've seen preconditions already: we've seen the
# @given(...)
# decorator, which tells us what input strategy to use.
# We can further refine the precondition by putting in constraints like
# for example:
# @given(st.integers(min_value = 0, max_value = 1000000))

# Here, the precondition (in words) is that
# "The input is an integer between 0 and 1,000,000, inclusive."

# Divide by zero example
# input two integers
def divide(x, y):
    return x / y

@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = 1, max_value = 1000),
)
@settings(max_examples=1000)
@pytest.mark.xfail
def test_divide(x, y):
    # what to test here?
    z = divide(x, y)
    # Spec ideas:
    # z is less than the difference between x and y
    assert z < abs(x - y)
    # ^^ seems to be true -- but fails for a rare input set,
    # e.g. x = 2, y = 1

# We couldn't even test our statement, because our program
# crashed :(
# Exception handling?
# this is exactly what preconditions are for.
# Let's directly make sure the thing we are dividing by (y)
# is > 0.

# Q: How do we exclude only zero?
# A: Use an assume statement
@given(
    st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = -1000, max_value = 1000),
)
@settings(max_examples=1000)
def test_divide_2(x, y):
    # Assume statement!
    # Adds some constraint to the precondition.
    assume(y != 0)
    assert type(divide(x, y)) is float

# Another bit of useful syntax:
# As we've seen, Hypothesis tests are run through pytest,
# which is Python's unit testing framework. We can use
# @pytest.mark.skip(reason = "Reason")
# @pytest.mark.xfail
# To mark a test as either ignored, or expected to fail.

# Also useful:
# @example(...)
# @settings(...)

"""
You can often read off preconditions from the documentation!
Examples:
- list pop: https://docs.python.org/3/tutorial/datastructures.html

    "It raises an IndexError if the list is empty or the index is outside the list range."

    This is another way of saying that the precondition of
    list.pop() is that the list should be nonempty.

- file open: https://docs.python.org/3/library/functions.html#open

    Has a number of preconditions:
    - The file should be able to be opened (OSError otherwise)

    - "If closefd is False and a file descriptor rather than a filename was given, the underlying file descriptor will be kept open when the file is closed. If a filename is given closefd must be True (the default); otherwise, an error will be raised."

Point: exceptions are often used to enforce preconditions --
if we don't know what to do on a particular input, we crash the program

Note that we can model exceptions in our specification in two
ways:
- If the exception is expected behavior, we can test that
  when the function is run on the bad input, the exception is raised.
  This does NOT involve excluding the input via the precondition,
  instead we write an assertion to expect the correct behavior.

- If the exception is not expected behavior, or if we don't
  want to consider inputs for which the exception is raised
  as valid, we can exclude them via a precondition.
"""

# Recap:
# We looked at writing preconditions
# We learned two useful ways of writing preconditions:
# - @given syntax with explicit parameters
# - assume(...) syntax

# - Mentioned some other useful pytest/Hypothesis syntax.

############## where we left off for day 3 ############

"""
Day 4

Announcements:
- Waitlist update: cap increasing to 72
- Reminder: you can follow along (repo is pinned at the top of Piazza)
Commands you can run:
```
git fetch --all
git branch backup-changes
git reset --hard origin/main
```

- Questions about HW1?

Recap: ways of writing preconditions:
    @given constraints
    assume

PLAN (today and next time)
- assert vs assume
- poll
- more about strategies
- a few more notes about specs (may skip)
- discussion and limitations

Why is it called "assume"?

- Assert: This property should hold, if it doesn't, that's an
    error. I want to report a test failure.
- Assume: This property should hold, if it doesn't, I want to
    ignore this test.

"""

####################
###     Poll     ###
####################

# Is this program for sorting a list correct? :)

def sort_list(l):
    l = l.copy()
    return l

# The spec:
@given(st.lists(st.integers()))
def test_sort_list(l):
    assume(l == sorted(l))
    assert sort_list(l) == sorted(l)

# Form:
# https://forms.gle/fGggQAeCj8y1obnX7

"""

Multiverse view
- Quantum bogosort:
    https://wiki.c2.com/?QuantumBogoSort
- (Based on: bogosort
    https://en.wikipedia.org/wiki/Bogosort)

TL;DR:
Assume is weird
We use it to assume certain properties are true of the input.
Another way of thinking about this is, whose responsibility is
it to ensure the list is sorted?
- If I use assume, I'm saying it's the caller's responsibility.
- If I use assert, in a specification to say that some property
  is true, then I'm saying it's the function's responsibility
  to guarantee that property.

Point:
We can think of the precondition as part of the spec!
Why?

Recall: a spec is just a true or false property about the program.
def example_test(x):
    assume(P(x))
    output = function(x)
    assert(Q(output))

We can think of the spec for this as the following statement:
    "On all inputs x such that P(x) holds, Q(function(x)) holds."
"""

def divides_2(x, y):
    return x / y

ERROR = .000001

@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
)
def test_divides_2(x, y):
    # could do e.g.:
    # assume -100 <= y <= 100
    assume(y != 0)
    result = divides_2(x, y)
    assert (result * y - x < ERROR)

"""
With the precondition included, the spec says:
On all inputs x, y such that
        -100 <= x <= 100 and
        -100 <= y <= 100 and
        y is not zero,
    divides_2(x, y) * y is approximately x.

Rough definition of specifications in Hypothesis:
- On all inputs such that all assume() statements
  hold, after executing the program all assert() statements hold.

This definition assumes that assume() is called before assert().
TRIVIA: In this case, the assume() is called a precondition
(as we have seen), and the assert() is called a "postcondition".
"""

######################
###     Part 2     ###
######################
# More about strategies

"""
NOT part of the spec:
- the program
- the strategy (generator)

We've seen some strategies already:
- st.integers()
- st.lists() -- given as a parameter a base strategy
    for generating elements of theh list.

What is the difference between a strategy and a precondition?
    st.lists(st.integers(), min_length = 1)
The strategy is an st.lists object, the precondition is just
the statement "l is a list of integers of length at least 1."

Example strategies:
(written as Python generators)
"""

def gen_simple():
    # generate sequential inputs
    for i in range(0, 1000):
        yield i

from random import randint

def gen_smarter():
    # generate completely random inputs
    # import a random number generator
    while True:
        yield randint(-10000, 10000)
    # Also not perfect and you can do better.

def gen_simpler():
    while True:
        yield 7
    # Probably not a good strategy
    # https://imgur.com/uR4WuQ0

"""
Some other useful strategies:
- st.text() -- for generating (valid) strings
- st.one_of() -- generates one thing or the other
    st.one_of(st.integers(), st.floats())
- st.functions() -- generates functions with a given signature

Hypothesis generators are much smarter than just generating
random values.

Minimizing examples:
    https://hypothesis.readthedocs.io/en/latest/data.html
    Once Hypothesis finds a failing example, it doesn't give up,
    it will continue searching to find a "minimal" example
    to show to the user

Custom formats: (emails, dates, etc.)
    st.text() -- UTF8 by default
    st.datetimes()
    st.emails()
    (you can also write your own)

Guiding the search:
    assumptions: https://hypothesis.readthedocs.io/en/latest/details.html#making-assumptions
    target: https://hypothesis.readthedocs.io/en/latest/details.html#hypothesis.target
"""

@given(st.floats(0, 1e100), st.floats(0, 1e100), st.floats(0, 1e100))
@pytest.mark.skip
def test_associativity_with_target(a, b, c):
    ab_c = (a + b) + c
    a_bc = a + (b + c)
    difference = abs(ab_c - a_bc)
    target(difference)  # Without this, the test almost always passes
    assert difference < 2.0

"""
Summary:
How hypothesis works, roughly:

1. Generate a random example

2. Run the example

    a. If it encounters a precondition/assume:
        does it satisfy the precondition?
        - If YES, continue
        - If NO, move on to the next test
            + on the next run, try to guide the search towards a passing example

    b. If it encounters an assertion:
        does it satisfy the assertion?
        - If YES, continue
            + on the next run, try to guide the search towards a failing example
        - If NO, report a failure -- go to step 4

4. Once a failing assertion is found:
    try to simplify the example ("shrink") it to something understandable.
"""

############## where we left off for day 4 ############

"""
Day 5

Announcements:
- HW1 due week from today
- Waitlist
I indicated my pref to update the cap to 72
- one of the 3, guaranteed (up to 63)
- up to 65, very likely
- beyond that, I can't guarantee but joining the waitlist helps show that there is a demand!

- Questions about HW1

**Reminder to clone the repo**

Plan:
- POLL
- Assume/assert recap
- Preconditions, postconditions, and beyond
- Limitations
"""

####################
###     Poll     ###
####################

"""
Which of the following has no effect? (Select all that apply)

1. assert True
2. assert False
3. assume True
4. assume False

https://forms.gle/KQivFbEyYNfxf2d48
https://tinyurl.com/3frmvxc8
"""

"""
Recall:

- assert means: if the property is not true,
    raise an error.

- assume means: if the property is not ture,
    ignore this branch of computation.

OR (provacatively):
- assume as "if the property is not true, destroy the universe"

Q: Why is assume useful?

There are going to be cases where there is an
invariant that should hold when a function is
executed. It makes sense (both for the programmer
and for the test case writer) to assume that the
property holds so that we don't consider edge
cases where it doesn't hold.

Q: Why don't you just handle every edge case in every function?

Reasons?

A1: You can't.
In Python you might be passed some weird/invalid input or type that you don't really know what it is.
def f(x):
    result = x + 1
    print(result)
    return True

Python has what's called "duck typing" which means
- if it acts like a duck and if it talks like duck,
    then it is a duck.
- if it has an x + 1 function, and x + 1 can be printed, then x is a valid input.

Response: why not just specify the types and
enforce them?
You can for example do this using something like
mypy
Mypy is a static type checker for Python.

A2: You're saving yourself work because
you're only testing for the cases you actually
care about rather than the edge cases where
some error occurs.

A3: It's inefficient!!!

If I re-check the invariants on every single
function call, my code will be very inefficient.
It's a significant performance overhead

In OOP it's common to have certain data invariants
that your class enforces.
"""

class MyPerson:
    def __init__(self, name, age):
        # What are the invariants?
        # Here, we assume self is an object
        # with a name and an age field.
        # self.name = name
        # self.age = age

        # You might even want to add other invariants, for example name should be nonempty,
        # age should be between 0 and 120
        # It's good OOP style to check these in the constructor.
        if age < 0 or age > 120:
            raise ValueError("age should be between 0 and 120")
        self.age = age
        if name == "":
            raise ValueError("name should be nonempty")
        self.name = name

    def get_age(self):
        # If you want to re-check invariants
        # on every function call.. this is annoying!
        # We first have to check that self.age and self.name exist
        # assert "age" in self.__dir__ # ???
        # We have to check that age and name
        # satisfy the invariants
        assert self.age >= 0
        assert self.age <= 120
        # ...
        return self.age

    # But this is inefficient! We have to recheck
    # on every call, and we already know that the
    # invariants hold.
    # Because we checked it -- in the constructor.
    # So if they don't hold, the user of the class
    # probably did something terribly terribly wrong

# Exercise: break the class invariant in Python
# We can do this because Python doesn't protect us
# from users misusing our invariants :(

# However, rather than check the invariants again
# on every method call, it's better style to
# assume that the user of the class is using
# your class appropriately, and it's more efficient
# because it doesn't result in unnecessary overheads
# on every method call.

"""
A3 (recap): assume reduces performance
overhead on each function call

A4: assume is also more efficient in compiled
languages because it allows compiler optimizations.

when I write a function like

def process_bool(b):
    if b:
        print("everything went OK")
    else:
        assume(False)

Another word for assume(False) is "unreachable"
Some languages have an unreachable macro: it
tells the compiler this branch of code should not
be reachable

That means the compiler can optimize the code!

Optimize the code to:
def process_bool(b):
    print("Everything went OK.")

We couldn't do this if the else branch
was an assert instead of an assume.
"""

######################
###     Part 3     ###
######################
# Preconditions, postconditions, and beyond
# We will probably have to skip most of this
# for time

"""
As we have seen, there are many different specifications
that can be written for a function.
We can speak about these being weaker or stronger than each other...

- Weaker: Less specific, more programs satisfy it
- Stronger: More specific, fewer programs satisfy it

Preconditions affect how many programs satisfy the spec.

Recall a precondition is an assume statement on the input.

- Weaker precondition ==> fewer programs satisfy the spec,
                      ==> stronger spec

- Stronger precondition ==> more programs satisfy the spec,
                        ==> weaker spec

The weakest possible specification is one that is always true,
regardless of the function:

    def test_weakest_spec():
        assert True

Of course, this is rather pointless, but it is a specification!

Similarly, the strongest possible specification is one that is
always false, regardless of the function:

    def test_strongest_spec():
        assert False

This is also not very useful, as it is not true of any function.
But again, it is a specification!

What about "postconditions"?

A postcondition is an assertion after executing
the program, on the program output.

If a precondition is an assumption on the input,
a postcondition is an assertion on the output.

Most/almost all of the specs we have seen before
are preconditions and postconditions.

"""

# SKIP
def count_unique(l):
    """
    Given a list l, returns the number of unique elements in l.
    """
    unique = 0
    l = l.copy()
    while l != []:
        x = l.pop()
        if x not in l:
            unique += 1
    return unique

"""
Preconditions and postconditions?

Some postconditions

The output is always an integer.
(weaker postcondition)

The output is between 0 and the length of the input list, inclusive.
(slightly stronger)

The output is equal to a standard implementation of the same function.
(strongest possible postcondition)
"""

"""
=== Advanced ===

Most of what we've done is based on preconditions
and postconditions,
but remember that a spec is just a true or false
property that we want the program to satisfy.
That means that specs can be much stronger
and more complicated than just describing
pre/post conditions

One way of doing this that we've seen is to
add assume() and assert() throughout the body
of the function, for example.

Even stronger properties??

- Behavior on multiple runs??
- The output of the function is equal to len(set(l)),
AND if the function is called again with the same input list,
it returns the same output again.

"Behavior of the function on a single run"
is called "functional correctness."

Everything we have seen so far is just about functional correctness.
But, keep in mind we could talk about stronger
properties if we wanted to.
"""

######################
###     Part 4     ###
######################
# Discussion and limitations

"""
Hypothesis

### Advantages

Some more about advantages:
https://news.ycombinator.com/item?id=34450736

"I've never introduced property tests [Hypothesis specs] without finding a bug in either the specification or implementation. I have repeatedly spent time figuring out where the bug was in my property testing library before realising that it was correct and the obviously correct code I was testing was actually wrong."

### Disadvantages

Most important limitation:

- Testing might not find the bug!

Edsger Dijkstra:
"Program testing can be a very effective way to show the presence of bugs, but it is hopelessly inadequate for showing their absence."

This is not a problem with the spec itself, but with using random testing
as a method of validating the spec.

Other limitations:
these are not specific to Hypothesis (!)

- Specification could be wrong

- Specification could be incomplete

There are a few other limitations on HW1 (part 2).

Other limitations of Hypothesis specifically?

- Customization

- Testing can be redundant.

Quick recap:
- we talked more about assert/assume
- why is assume useful? why are invariants useful?
- we talked about postconditions:
    most of the specs so far have been postconditions
    on the output.
    A pre/post condition based spec is called
    functional correctness
- we talked about limitations of Hypothesis: it can't
    prove there are no bugs.
    That is what the remaining tools in this class
    will be about.

"""
