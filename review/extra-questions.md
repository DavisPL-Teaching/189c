# Extra study questions

## Module 1: Correctness, Specifications, Hypothesis

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

2. The following is a program with an assume and assert statement.
Fill in the blank so that the program satisfies the spec.
Your predicate may refer to x or y, but it should be true for at
least one input (so you can't just write "false").

```
x = get_user_input()
y = double(x)
assume ______
assert y == 8
```

3. Which of the following is NOT a reason Hypothesis might fail to catch a bug?

A. The program is actually correct (there are no bugs)
B. The random generator failed to generate an example which finds the bug
C. The postcondition written was satisfied, but too weak (not specific enough)
D. The postcondition written was satisfied, but too strong (too specific)
E. The precondition excluded the possibility of a bug
F. The specification written was totally wrong (did not properly describe the
    correct behavior of the program)
G. The program timed out or took too long to run

## Module 2: Z3 and Satisfiability

4. Is the following formula satisfiable or unsatisfiable?
Here, x is an integer.

    (x > -5 OR x < 5) AND abs(x) >= 10

5. What is the difference between a Z3 variable and a Python variable?
(short answer)

6. Write a regular expression to match the set of license plates represented
by 3 capital letters, followed by a space, followed by 3 numbers.
Syntax you may use:
- z3.Range("a", "z"): matches a lowercase letter
- z3.Range("A", "Z"): matches a capital letter
- z3.Range("0", "9"): matches a digit
- z3.Concat(R1, R2): matches R1 followed by R2 (Concat can also have more than 2 arguments)
- z3.Union(R1, R2): matches R1 or R2
- z3.Re(s): matches exactly the string s
- z3.Star(R): a sequence of 0 or more strings matching R

## Module 3: Dafny and formal verification

7. Which of the following is likely the most effort-intensive tool to use
for providing some validation that a program is correct?

A. Writing some unit tests
B. Hypothesis
C. Z3
D. Dafny
E. Rust

8. Fill in the weakest precondition for the following function,
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

9. The following is a function with a missing loop invariant.
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

## Module 4: Rust and Safety Properties

10. Explain why the following IS or IS NOT a safety property:

"The function f always takes as input an integer and returns an integer."
