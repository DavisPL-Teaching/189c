# Lecture 4: Z3 Applications

## Announcements

- HW2 is out! Due Friday, May 3.

## Plan for the next few days

Using Z3 for some fun programming projects.

## Looking ahead

- Strings and regular expressions
- Functions, arrays, etc.
- Z3 internals
- Z3 limitations
- Then moving on to Dafny (HW4) and Rust (HW5).

## Recap

We've been doing lots of mini examples to get a feel for Z3 syntax.
We've seen how to:

- Encode specifications as Z3 formulas

- Use Z3 to answer questions about the spec, such as:

  + Is the spec true for all inputs? (theorem proving)
  + Is the spec true for at least one input? (satisfiability)
  + What are *all* possible solutions? (enumeration)
  + Is spec1 stronger or weaker than spec2?

## Today (Day 9)

Before we get into more advanced data types, let's do some
some larger projects to see how Z3 can be used in practice.

Along the way, we should learn:

- How to go about encoding a problem in Z3
  1. What are the variables?
  2. What are the constraints?
  3. What are the properties we want to check?

- How to think logically about problems
  + Describing the *what* instead of the *how*

- How to debug when Z3 gives unexpected results

Things we won't learn (yet):

- Tricks to make Z3 run faster

- Limitations of Z3
  + Many people asked, what sorts of problems will Z3 say Unknown for?
  + You will see an example on the homework (part 3)

- More advanced applications of Z3
  + Often use Strings, Arrays, Functions, etc.

## Poll

The poll will be to decide which project to do :)

See projects in the projects/ folder.
