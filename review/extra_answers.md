# Answers to the extra study questions

1. A, C, D, E

2. Valid answers include:
- assume x == 4
- assume y == 8

3.
(a) Yes, it IS a functional correctness property because it only depends on the function's input/output behavior.
(b) Yes, it IS a safety property because it is of the form "bad thing does not happen" where

    BAD THING = f returns something that is not a non-integer

4. D (The postcondition written was satisfied, but too strong)

5. Satisfiable

6. Valid answers include:
- A Z3 variable represents all possible inputs, not just a single input.
- A Z3 variable is a symbol (like x or y), not a specific value

7. True

8. D (Dafny)

9. Valid answers include:
- x >= 3
- x + x >= 5
(these preconditions are equivalent; should be equivalent to one of the above)

10.
(a) satisfies (i), (ii) but not (iii)
(b) satisfies (i), (iii) but not (ii)
