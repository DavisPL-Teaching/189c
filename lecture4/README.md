# Lecture 4: Z3 Applications

## Announcements

- HW2 is out! Due Friday, May 3 (11:59pm)

- In case you haven't seen it, if you're having any GitHub Classroom issues:
https://piazza.com/class/lt90i40zrot3ue/post/48

- Any questions about HW2?

## Plan for the next few days

Applications of Z3 to some fun programming problems.

## Looking ahead

Try to unleash the full power of Z3:
- Strings and regular expressions
- Functions, arrays, etc.
- Z3 internals
- Z3 limitations

Then moving on to Dafny (HW4) and Rust (HW5).

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
some larger problems.

Main goal:
- Learn how you might incorporate Z3 into practical
  programming tasks.

Along the way, we should also learn:

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

The poll will be to decide which problem to do :)
(see the problems/ folder)

https://forms.gle/cPFSMh2Y13nmyi1i9
https://tinyurl.com/yeyvks6h

### Brief description of the problems

- Sudoku solver
  Given a 9x9 Sudoku board, find a solution to the Sudoku puzzle

- 8 queens problem
  Famous chess puzzle (not really about chess)
  Place 8 queens on an 8x8 chessboard so that no two queens attack each other
  "Attack" means moving diagonally, horizontally, or vertically

- Seating arrangement generator
  Imagine you're inviting a bunch of people over for dinner
  You want to seat them all around a round table
  but certain pairs of them don't get along and might generate
  heated arguments, which you want to avoid.
  Can we automatically generate a seating arrangement?

- Task scheduler
  We have a bunch of tasks, including
  + duration of the task
  + deadline of the task
  Can we schedule all the tasks so that they all get done?

- FRACTRAN program optimizer
  FRACTRAN is an "esoteric programming language"
  Esoteric programming languages are typically minimal
  syntax languages that make it easy to write a program
  interpreter or compiler, and which are expressive enough
  for arbitrary programs (Turing complete), but probably
  don't have many practical and convenient features.
  Designed to be extremely minimal.
  FRACTRAN is one particular such minimal language.
  We can use Z3 to answer questions about a program,
  and even to optimize a program.

  Two classical program optimizations:
  + Dead code elimination
    If there's a piece of your program that isn't needed,
    delete it.
  + Constant propagation
    If you know the value of a variable at a certain point,
    replace all uses of that variable with the constant value.

- Travelling salesperson problem
  Given a list of cities and the distances between each pair of cities,
  what is the shortest possible route that visits each city exactly once
  and returns to the origin city?

- Other: if you want to propose something

## Disclaimers/notes

I didn't try solving the problems ahead of time!
We will discover along the way if there are any unexpected
roadblocks and how to overcome them.

I'm leaving on copilot suggestions for now
(Because this is a sort of more open-ended exploration)
But I'll turn it off if it gets too distracting.
