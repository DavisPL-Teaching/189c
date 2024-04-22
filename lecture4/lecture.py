"""
Lecture 4: Applications of Z3

Recap:
- We know that to ensure our programs are correct, we need to
  write specifications.
- We can use Z3 to help us write, understand, and prove specifications:

    + Is the spec true for all inputs? (theorem proving)
    + Is the spec true for at least one input? (satisfiability)
    + Can we get *all* possible inputs? (enumerating solutions)
    + Is spec1 stronger or weaker than spec2?

To solve a problem using Z3, we have to define and manipulate
*formulas* that represent the problem in Z3's logic.
We showed:

- Integers
- Booleans
- Real numbers
"""
