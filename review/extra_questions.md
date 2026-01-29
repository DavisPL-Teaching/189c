# Extra study questions

Extra study questions for the midterm and the final.

Midterm will cover through Lectures 1 and 2.

## Pre-Midterm

### Lecture 1: Correctness, Specifications, Hypothesis

1. Consider the following double function. Which of the following specs does
it satisfy?
(select all that apply)

```
def double(x):
    return x + x
```

Assume x is an integer and let `y = double(x)`.

A. Precondition x is even, postcondition y is even
B. Precondition x is odd, postcondition y is odd
C. Precondition x == 5, postcondition y == 10 or y == -10
D. The program never crashes with a type error
E. On every input, the program terminates

2.
(a) Explain why the following IS or IS NOT a functional correctness property.
(b) Explain why the following IS or IS NOT a safety property.

    "For any input x, the function f always returns an integer."

3. The following is a program with an assume and assert statement.
Fill in the blank so that the program satisfies the spec.
Your predicate may refer to x or y, but it should be true for at
least one input (so you can't just write "false").

```
x = get_user_input()
y = double(x)
assume ______
assert y == 8
```

4. Which of the following is NOT a reason Hypothesis might fail to catch a bug?
(select all that apply)

A. The program is actually correct (there are no bugs)
B. The random generator failed to generate an example which finds the bug
C. The postcondition written was satisfied, but too weak (not specific enough)
D. The postcondition written was satisfied, but too strong (too specific)
E. The precondition excluded the possibility of a bug
F. The specification written was totally wrong (did not properly describe the
    correct behavior of the program)
G. The program timed out or took too long to run

### Lecture 2: Z3 and Satisfiability

5. Is the following formula satisfiable or unsatisfiable?
Here, x is an integer.

    (x > -5 OR x < 5) AND abs(x) >= 10

6. What is the difference between a Z3 variable and a Python variable?
(short answer)

7. True or false: if z3.Implies(spec1, spec2) is provable, then spec1 is
stronger than spec2.

## Post-midterm

### Lecture 3: Advanced Z3

TBD

### Lecture 4: Dafny and interactive verification

8. Which of the following is likely the most effort-intensive tool to use
for providing some validation that a program is correct?

A. Writing some unit tests
B. Hypothesis
C. Z3
D. Dafny
E. Rust

9. Fill in the weakest precondition for the following function,
given the postcondition.
It can be anything that is equivalent to the correct answer.
You won't be graded on syntax; only on whether your answer is conceptually correct.
```
method Double(x: int) returns (y: int)
    requires _______
    ensures y >= 5
{
    y := x + x;
}
```

10. The following is a function with a missing loop invariant.
For the possible loop invariants (a) and (b),
which of the three loop invariant properties (i)-(iii)
does it satisfy?
Briefly explain your reasoning for each one.

```
method AddOne(a: int) returns (b: int)
    requires a >= 0
    ensures b == a + 1
{
  b := 0;
  while b < a + 1
    invariant ______
  {
    b := b + 1;
  }
}
```

(a) invariant b >= 0
(b) invariant b <= a
