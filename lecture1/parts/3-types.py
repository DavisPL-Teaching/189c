"""
Lecture 1, Part 3:
Types of Specifications

=== Intro ===

From last time: S1 is stronger than S2 if
all programs satisfying S1 also satisfy S2.

"stronger than" works how you would expect! for example:

- If S1 is stronger than S2 and S2 is stronger than S3, then S1 is stronger than S3.

Thinking about how strong you want your specification to be is an important part of testing
and verifying software correctness in practice!

    ==> Weaker specs are often easier to test and verify, but they leave room for mistakes!

    ==> Stronger specs are often harder to write, but
        can be more likely to find bugs --
        however, it can be difficult to ensure that the
        spec covers all cases (more about this in today's lecture).

=== Poll ===

Sort the following specifications in Hypothesis by which row is stronger than each column.
That is, check the box if the specification in that row is stronger than the specification in that column.

1. @given(x==1 or x==2), assert f(x) == x
2. @given(x==1), assert f(x) == x
3. @given(x==2), assert f(x) == x
4. @given(x==3), assert f(x) == x
5. f does not crash on inputs x==1 and x==2.

Poll link:
https://forms.gle/kAUYts452mbqSypD9

Answers?
.
.
.
.
.

1 is stronger than 1 because any spec is stronger than itself

1 and 2: is 1 stronger than 2 or 2 stronger than 1?

1 is stronger than 2:

    def stronger:

        "any program satisfying 1 satisfies 2"

    - 1 is testing the program f on a *broader range* of inputs

        if 1 is the case, then I can in particular run
        the program on x == 1, and I will get spec 2.

        Similarly, if 1 is in the case, then I can in particular
        run the program on x == 2, and I will get spec 3.

Question: but isn't "x == 1 or x == 2" weaker than just "x == 1"?

    If we have a weaker statement about the input, we get a stronger
    spec!

    Because there are more inputs that the program has to
    follow, we get a stronger spec.

    If you expand the set of inputs, you get a stronger spec.

    as a venn diagram?
    spec S1 is stronger than S2
    means
    the set of programs satisfying S1 is a subset of the set
    of programs satisfying S2, which means

    S1 (thought of as a set of programs) is a smaller circle
    inside S2.

Another way of thinking about it:

    1 is saying: f(1) == 1 and f(2) == 2
    2 is saying: f(1) == 1
    3 is saying: f(2) == 2

so 1 is stronger than 2 and 3.

Answers:
    1 stronger than 1, 2, 3, 5
    2 is stronger than 2
    3 is stronger than 3
    4 is stronger than 4
    5 is stronger than 5
"""

# Imports
import pytest
from hypothesis import given
from hypothesis import strategies as st
from hypothesis import settings

"""
.
.
.
.
.

=== Types of Specifications ===

Our definition of "specification" is very broad:

    "any true or false property"

this is very useful! But it is also not very specific.

In practice, we need our specification to be understandable to the tool we are using...
    i.e.: written in a more specific grammar

Ex:

- Python unit tests can only write assertions that are expressible in Python syntax

- Hypothesis only understands specs using @given annotations on pytests and assertions

- We may be testing a function that we didn't implement! (or a foreign API, such
  as a network API)
  If so, we can only test statements that are true *before* and *after* the program executes

    These are called preconditions and postconditions

We can express these "statements that are true" using formal logic syntax.

- for all, there exists, if-then, and, or, not, ...

Here are some examples (some previous and some new ones) on integer_sqrt:

1. If the input is an integer, then the output is an integer.

    assert typeof(output) is int

    Let's think of our program integer_sqrt, as just a function f

    For all x, if typeof(x) is int then typeof(f(x)) is int.

2. False (false of all programs) (empty set of programs)

    assert false

3. If the input is greater than or equal to 100, then the output is greater than or equal to 10.

    For all x, if x ≥ 100 then f(x) ≥ 10

4. The program terminates on all inputs.

    For all x, f(x) exists?
    ^^ maybe expressible using logic?

5. The program does not read any files from the filesystem

    ???
    Check the journal log of the computer?
    We would need some way to log all of the function calls
    (in this case system calls) that are made by f when it executes.
    This would be somewhat difficult to do in Hypothesis alone.

^^ More on these soon!
"""

from math import sqrt
def integer_sqrt(n):
    return int(sqrt(n))

# Spec 3 as a Hypothesis test
# @pytest.mark.skip
@given(st.integers(min_value = 100, max_value = 1000))
def test_spec_3(n):
    assert integer_sqrt(n) >= 10

# Spec 4 as a Hypothesis test?
@given(st.integers(min_value = -1000, max_value = 1000))
@pytest.mark.skip
def test_spec_4(n):
    # ensure that program terminates for n...
    # I can run the program...
    ans = integer_sqrt(n)
    # ^^^ if the program terminates, great!
    # ^^^ if the program doesn't terminate... we have a problem
    # our test also just won't terminate.
    # TODO ...
    # assert ???
    raise NotImplementedError

"""
The discussion about which are testable using Hypothesis might leave
you wondering what properties exactly *can* be tested using Hypothesis
(or easily tested in general)?

===== Functional correctness =====

An important pattern:

    For some of the specs above, we were able to write the spec
    just thinking about what's true
    before/after the program executes.

        --> solely about the input/output behavior of the function

    Like testing a foreign function!
        e.g. connecting to Google, GitHub, or chatGPT network
        API

- A **functional correctness** property is a spec which only depends
  on the set of all ordered pairs (x, y) such that f(x) = y.

Functional correctness is the focus of many program testing and
verification efforts in practice.
It's not perfect, but it is often a good starting point!
And we have good tools for reasoning about it (compared to some of the others
which require deep and difficult encodings, more on this later.)

- Often other properties can be encoded as functional correctness
  by maintaining some additional "state".

Informally:
    functional correctness = property of a program that only
    depends on its input-output behavior.

But even "True" and "False" are examples of this which aren't very useful.
Also "if the input is an integer, then the output is an integer"
isn't very useful.
More useful:

- A **full functional correctness** spec is one which exactly specifies
    what f should do on every input.

    There is a Q on the HW which asks you to write a full
    functional correctness spec!

    That means: for all x, f(x) is exactly the value y

    Pragmatically, it means...

        if you write a Hypothesis test, you should go
        through every piece of data in your output, and
        verify that every piece of data was computed
        correctly.

    Example: if we say "whenever x is an integer, f(x) is an integer", this doesn't define which integer it is!
    but in our example:

        "for all integers x, y = int_sqrt(x) is an integer such that y * y <= x < (y + 1) * (y + 1)"

    can actually show that there is only one such y.
    So this is a full functional correctness spec.

    ASIDE (for those interested): more formally, it means
    our spec should satisfy a functional property like

        For any f1, f2 satisfying the spec S, if f1(x) = y1 and f2(x) = y2
        then y1 == y2.

Examples:

    "int_sqrt(x) is always odd"
    is this functional correctness? Yes
    is this full functional correctness? No

    "int_sqrt(x) is odd on at least two inputs"
    is this functional correctness? Yes
    is this full functional correctness? No

    "int_sqrt(x) takes less than 5 minutes to run"
    is this functional correctness? No
    is this full functional correctness? No

    "int_sqrt(x) does not read your password from memory"
    is this functional correctness? No
    is this full functional correctness? No

Observation:

    Full functional correctness is stronger than functional correctness.
"""

"""
A common way to express (full) functional correctness
is using...

===== Preconditions and postconditions =====

    (A.k.a.: "Programming by Contract")
    (A.k.a.: "Hoare triples")

    "An Axiomatic Basis for Computer Programming"
    Tony C.A.R. Hoare, 1969

A pre/postcondition spec has the following form:

    P and Q: Boolean properties

    - if P is true before executing the program,
        and we execute f,
      Q is true after.

In other words:

    - for ALL inputs satisfying P, after executing program
      f, the output satisfies Q.

We often use preconditions and postconditions to express functional correctness specs.
"""

# Classic example: Division by zero

# input two integers
def divide(x, y):
    # (integer division)
    return x // y

# @pytest.mark.xfail
@given(
    st.integers(min_value = -1000, max_value = 1000),
    # st.integers(min_value = -1000, max_value = 1000),
    st.integers(min_value = 1, max_value = 1000),
    # st.integers(min_value = 0, max_value = 1000),
)
# @settings(max_examples=1000)
# @pytest.mark.skip
def test_divide(x, y):
    # what to test here?
    # Write the spec here:
    # (you could write any spec here, but let's use:)
    z = divide(x, y)
    assert z * y <= x < (z + 1) * y

    # Fixed version with added precondition
    # if y > 0:
    #     z = divide(x, y)
    #     assert z * y <= x < (z + 1) * y

# We couldn't even test our statement, because our program
# crashed :(
# Exception handling?
# this is exactly what preconditions are for.
# Let's directly make sure the thing we are dividing by (y)
# is > 0.

"""
The condition

    st.integers(min_value = 1, max_value = 1000),

is implicitly a precondition! It tells Hypothesis:

    "I only care about inputs y between 1 and 1000"

Difference between preconditions and regular assertions -

    Preconditions exclude some inputs from consideration

    Even if the program crashes or misbehaves wildly on
    other inputs, I won't catch it.

Exercise (skip for time)
Rewrite the examples 1-7 using preconditions/postconditions

Even if you have not heard of the word "precondition",
you are probably intuitively familiar with the concept of preconditions
if you have some experience programming and working with libraries...

Examples:
- list pop: https://docs.python.org/3/tutorial/datastructures.html

    "It raises an IndexError if the list is empty or the index is outside the list range."

    This is another way of saying that the precondition of
    list.pop() is that the list should be nonempty.

    Implicit preconditions:
    - input is a list
    - input should be nonempty

    pre/post style spec:

    "if you generate inputs that are lists and are nonempty,
                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                      precondition
     and run the progam, then the output will satisfy ...."
                                                ^^^^^^^^^^
                                                postcondition

- file open: https://docs.python.org/3/library/functions.html#open

    Has a number of preconditions:
    - The file should be able to be opened (OSError otherwise)

    - "If closefd is False and a file descriptor rather than a filename was given, the underlying file descriptor will be kept open when the file is closed. If a filename is given closefd must be True (the default); otherwise, an error will be raised."

Point:
You can often read off preconditions from the documentation!

There are always implicit assumptions in any API that you use.

Point:
Often a precondition that's useful is whatever is needed to not
have the program crash or otherwise misbehave.

In practice, exceptions are often used to enforce preconditions --
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

Another example:

(skip for time)
"""

def divides_2(x, y):
    return x / y

ERROR = .000001

@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
    # st.integers(min_value = 1, max_value = 100),
)
# @pytest.mark.skip
def test_divides_2(x, y):
    if y != 0:
        result = divides_2(x, y)
        assert (result * y - x < ERROR)
        assert (result * y - x > -ERROR)
    # ^^^ Note: not a full functional correctness spec
    # hard to pin down the exact value in the case of
    # approximate floating point arithmetic.

"""
With the precondition included, the spec says:
On all inputs x, y such that
        -100 <= x <= 100 and
        -100 <= y <= 100 and
        y is not zero,
    divides_2(x, y) * y is approximately x.

More generally, the spec has the following form:

    "On all inputs x such that P(x) holds, Q(f(x)) holds."

Are pre and postconditions sufficient?

- Can we now express all properties we are interested in?

- Can Hypothesis express anything that pre/postconditions can't?

A: Yes
    - Runtime? we could write a Hypothesis test that times the program
      (using time.time or something)
    - What about running the program multiple times?
        e.g.: test that the program is deterministic
            y1 = f(x)
            y2 = f(x)
            assert y1 == y2
    - What about asserting something inside the program?
        Put assertions inside your program
        and assertions before/after running different programs
        so, you don't only have to assert things at the end.

More general way of thinking about the
kind of specifications that Hypothesis can support?

A sneak peak: preconditions can be written using "assume". This is what
we will cover next.
"""

from hypothesis import assume

def divides_2(x, y):
    return x / y

ERROR = .000001

@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
)
@pytest.mark.skip
def test_divides_2(x, y):
    assume(y != 0) # assume statement!
                   # another way of expressing preconditions

    # equivalent to:
    # if y == 0:
    #     return

    result = divides_2(x, y)
    assert (result * y - x < ERROR)

def divides_2(x, y):
    return x / y

ERROR = .000001

@given(
    st.integers(min_value = -100, max_value = 100),
    st.integers(min_value = -100, max_value = 100),
)
@pytest.mark.skip
def test_divides_2(x, y):
    if y != 0:
        result = divides_2(x, y)
        assert (result * y - x < ERROR)

"""
=== Other types of specifications? ===

Recall these examples from before:

4. The program terminates on all inputs.

5. The program does not read any files from the filesystem

and others...

6. The program executes in constant time
7. The input arguments are not modified by the program.

You could try to write these in Hypothesis...
... but you would soon run into trouble.
"""

"""
Some questions:

- Are all of these specifications expressible as Hypothesis tests?

    No - some are, some aren't

- Are all of these specifications easily checkable?

    No - some are, some aren't

Other examples?
    (see cut/other-specs.md)

===== Safety and Liveness =====

Two other special cases of specifications that turn out to be particularly useful
(these are not functional correctness):

These have to do with the behavior of the program when run
(properties of the program trace):

- A **safety property** states that "for all x, when f(x) is run,
  some bad event X does not happen."

    "the program doesn't read any files"
    "the program doesn't modify its input x"

- A **liveness property** states that "for all x, when f(x) is run,
  some good event X does happen."

    "f(x) does terminate"

Neither of these can be specified using functional correctness...

    but they *are* examples of specifications (since they
    are true or false properties)
    and they are often useful in practice.

Are the above all possible specifications?
No! We can imagine much more interesting cases...
    (More examples, again, in cut/other-specs.md)

Questions:

Can we test safety properties in Hypothesis?

Can we test liveness properties in Hypothesis?

=== Conclusions ===

Review:

- Any testing or verification system is limited to a particular type of specs that it
  can express or support.

- Different ways of writing specs have different advantages and drawbacks!

- A common approach is to focus on properties about the input/output of a function:

    + functional correctness

    + full functional correctness

    + preconditions/postconditions

        (like @given and assert!)

- Beyond functional correctness: safety and liveness are two other example classes of specs
  that are often useful.

"""
