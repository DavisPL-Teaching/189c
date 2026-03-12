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

8. Z3 sees a formula or piece of syntax that it knows it is unable to solve,
   rather than believing that it can make progress.

9. C

10. E (branching can be applied here on either x or y, as neither of unit propagation or pure literal elim applies).

11. D (Dafny)

12. Valid answers include:
- x >= 3
- x + x >= 5
(these preconditions are equivalent; should be equivalent to one of the above)

13.
(a) satisfies (i), (ii) but not (iii)
(b) satisfies (i), (iii) but not (ii)
