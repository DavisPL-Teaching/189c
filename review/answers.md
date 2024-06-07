# Answers to the study questions

1. A, C, D, E

2. Valid answers include:
- assume x == 4
- assume y == 8

3. D (The postcondition written was satisfied, but too strong)

4. Satisfiable

5. Valid answers include:
- A Z3 variable represents all possible inputs, not just a single input.
- A Z3 variable is a symbol (like x or y), not a specific value

6. One possible answer:
z3.Concat(
    z3.Range("A", "Z"),
    z3.Range("A", "Z"),
    z3.Range("A", "Z"),
    z3.Re(" "),
    z3.Range("0", "9"),
    z3.Range("0", "9"),
    z3.Range("0", "9"),
)

7. D (Dafny)

8. Valid answers include:
- x >= 3
- x + x >= 5
(these preconditions are equivalent; should be equivalent to one of the above)

9.
(a) satisfies (i), (ii) but not (iii)
(b) satisfies (i), (iii) but not (ii)

10.
It is a safety property because it is of the form "bad thing never happens"
where:
bad thing == the program is called on input an integer and returns something
that is not an integer.

Also a valid interpretation:
bad thing == the program is called on an input that is not an integer,
OR the program is called on input an integer and returns something that is not
an integer.
