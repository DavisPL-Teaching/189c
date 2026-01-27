# Poll questions

## Module 1: Correctness, Specifications, Hypothesis

### April 5

Come up with a property that is true about the `square_root` function.
It should be more interesting than just the behavior on a single input. You can describe it in code or using words.

```
from math import sqrt

def square_root(x):
    return int(sqrt(x))
```

### April 8

Here are 3 programs, and 4 specifications. For each program, which
specification(s) does it satisfy?
For all programs, assume that the input is an arbitrary integer.

Programs:
```
def p1(x):
    return x + 1
def p2(x):
    return x + x
def p3(x):
    return x * x + 1
```

Specifications:
```
def s1(x):
    assert type(p(x)) is int
def s2(x):
    assert p(x) > x
def s3(x):
    assert p(x) == x * x
def s4(x):
    assert p(1) == 2
```

### April 10

Is sort_list correct according to the spec?

Program:
```
def sort_list(l):
    l = l.copy()
    return l
```

Spec:
```
@given(st.lists(st.integers()))
def test_sort_list(l):
    assume(l == sorted(l))
    assert sort_list(l) == sorted(l)
```

### April 12

Which of the following has no effect? (Select all that apply)

```
assert True
assert False
assume True
assume False
```

### April 15

Which of the following is a limitation of testing with Hypothesis? (Select all that apply)

- Testing can only demonstrate the presence of bugs, and can never prove their absence
- The specification written could be wrong (not what the user intended)
- The specification written could be incomplete (underspecified)
- It can only test preconditions and postconditions
- It can only test assume and assert statements

## Module 2: Z3 and Satisfiability

### April 17

What would you guess is the output of the following Z3 code?

```
def test_poll_output():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.And(x > 100, y < 100)
    prove(spec)
```

- "proved"
- "failed to prove"
- "counterexample" with no other text
- "counterexample" together with an example of x and y

### April 19

What would you guess is the output of the following Z3 code?

```
def test_poll_output_2():
    x = z3.Int('x')
    y = z3.Int('y')
    spec = z3.Implies(z3.And(x >= 10, y == x * x), y >= 100)
    prove(spec)
```

### April 22 (not a study question)

### April 24

Which of the following are correct difference(s) between a z3.Int and a Python integer?

- You can do + on Python integers, but not on Z3 integers
- You can do == on Python integers, but not on Z3 integers
- For Z3 integers, x == y returns a Z3 expression, not a concrete Boolean
- A Z3 integer is simply a symbol like "x" or "y", it does not have a known value
- Python integers are bounded, while Z3 integers are unbounded

### April 26

Which of the following is a likely **advantage** of using Z3 to solve a problem? (Select all that apply)

- Z3 will work with existing Python code directly without modification
- Separate out the WHAT of your problem (what the output should like) from HOW to get there
- Z3's constraint solving engine is likely faster and more powerful than what you could write by hand
- Z3 will always return a mathematically correct answer
- Z3 will always return a yes or no answer

### April 29

Which of the following are key differences between Hypothesis and Z3? (Select all that apply)

- Hypothesis takes as input a program and a spec; Z3 takinputes as  only a spec (if there is a program, it must be encoded)
- Hypothesis can generate counterexamples (to a spec), but Z3 can't
- Hypothesis can "prove" a spec for all inputs, but Z3 can't
- Z3 can be used as part of a larger program to generate examples and solve constraints
- They are both black boxes, but the internals are different: Hypothesis uses random input generation and Z3 uses math to come up with an answer.

### May 1

Which of the following is a good reason to use a Z3 variable instead of a Python variable?

- The value of the variable is unknown
- You want to consider all possible inputs at once, not just a particular input
- The variable is an input that is given to you
- The variable is an output that you want to solve for

### May 3 (no poll)

### May 6

What are some possible reasons that Z3 might return UNKNOWN? (Select all that apply)

- Use of a large number of Boolean and Integer variables
- Use of strings and regular expressions
- Use of functions and arrays
- Use of advanced quantifiers: z3.ForAll and z3.Exists
- Encoding a mathematically complex property, like an advanced mathematical theorem (e.g., Fermat's Last Theorem)

### May 8

Which of the following would be useful for a Z3 regular expression to match phone numbers?

- z3.Range("0", "9")
- z3.Re("-")
- z3.Length
- z3.Union
- z3.Concat
- z3.Star

(Optional) write the regular expression.

### May 10

Oh no, Z3 is hanging! What are some things to try?

- Spam ctrl-C and hope that it stops the program
- Add additional constraints to simplify the problem
- Bound the variables
- File a bug report with Z3
- Give up and use Hypothesis instead
- Try a different encoding of the problem
- Try a simpler example
- Try using simpler data types, like `z3.Int` instead of `z3.Array`

### May 13 (not a study question)

## Module 3: Dafny and formal verification

### May 15

What is formal verification?

- Generating a program that satisfies a given specification
- Proving that a program satisfies its specification
- Proving that a specification is precise enough to cover all inputs
- Testing whether a specification holds by generating random inputs
- Generating a counterexample to a specification if it does not hold

### May 17

Which of the following pre/postconditions for Double will allow both the method and the following test to pass?
(Select all that apply)

```
method Double(x: int) returns (y: int)
// requires ... ensures ...
{
   y := x + x;
}

method TestDouble()
{
   var x := Double(5);
   assert x == 10;
}
```

1. nothing (the test will pass as is)
2. requires x == 5
3. ensures y == 10
4. ensures y == x + x
5. requires x == 0 ensures y == x + x
6. requires x == 5 ensures y == 10
7. requires false
8. ensures false
9. requires (x == 5 ==> y == 10)
10. ensures (x == 5 ==> y == 10)

### May 20

Consider the following function:

```
method birthday(age: int) returns (new_age: int)
{
     return age + 1;
}
```

1. What is StrongestPostcondition(age >= 0) ?

2. What is WeakestPrecondition(new_age == age + 1 && new_age >= 0)?

### May 22

Which of the following is a correct description of the Weakest Precondition WP(program, Q) (where Q is the postcondition)?

- Describes the set of all inputs such that running the program on that input does not generate an error
- Describes the set of all inputs such that running the program on that input terminates
- Describes the set of all possible inputs such that after running the program, the output satisfies Q
- Describes the set of all possible outputs of the program after running on an input satisfying Q
- Describes the set of all possible outputs of the program, other than those outputs satisfying Q

## May 24

Write a loop invariant for `CopyInt`.
```
method CopyInt(a: nat) returns (b: nat)
    ensures b == a
{
    var i := a;
    b := 0;
    while i > 0
    // invariant ...
    {
        i := i - 1;
        b := b + 1;
    }
}
```

### May 29

Under which of the following circumstances is "false" a valid loop invariant?
(select all that apply)

- If the precondition is "true"
- If the precondition is "false"
- If the postcondition is "true"
- If the postcondition is "false"
- If the loop body is empty
- If the entire loop block is unreachable code

### May 31

Which of the following can be considered a major disadvantage of using Dafny? (Select all that apply)

- If Z3 returns SAT/COUNTEREXAMPLE, then Dafny may fail to prove a spec even if it's true
- If Z3 returns UNSAT/PROVED, then Dafny may fail to prove a spec even if it's true
- If Z3 returns UNKNOWN, then Dafny may fail to prove a spec even if it's true
- When using formal verification it is possible to prove wrong results
- Loop invariants cannot be generated automatically by the Dafny verification engine and have to be written by hand
- Formal verification can be very effort intensive
- Programs must be written in Dafny and can't be integrated into an existing Python or C code base

## Module 4: Rust and Safety Properties

### June 3

Which of the following are examples of safety properties?

- The program never crashes
- All values of type bool are always either 0 or 1
- The program never accesses invalid memory
- The program both reads and writes to the file "my_temp_file.txt"
- The program terminates
- The output of abs() is always nonnegative

### June 5

Which of the following safety properties does the Rust compiler aim to guarantee?

- Type safety: variables of a type always have a valid value of that type
- Panic safety: valid programs never panic (crash)
- Memory safety: the program never accesses invalid memory
- Termination: the program always terminates
- Data race freedom: multiple threads can never be engaged in a data race
- References: For any memory location, there is only one mutable reference OR any number of immutable references to that data at a given time. (Freebie! This is true and a crucial property about how Rust ensures memory safety, but we may not get to it in class.)
