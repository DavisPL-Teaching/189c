# Mid-quarter review

Review (list of topics) for the first half of the course:

## Hypothesis

- Correctness
  + Why is correctness important?
  + Definition of software correctness
- Specifications
  + writing specifications
  + complete specifications
- Writing specifications
  + assume and assert
  + preconditions and postconditions
  + specifications that go beyond logical assertions:
    "function does not terminate"
    "function is pure"
    "function does not print to stdout"
    etc.
- Methods of validating specifications
  + testing
  + limitations

## Z3

- Steps to solve a problem with Z3
  + declare variables
  + declare constraints
  + ask Z3 to solve or prove the constraints
- Basic data types
  + Int, Real, Bool
- Satisfiability
  + what is satisfiability?
  + how does prove() relate to satisfiability?
- Complex data types
  + Strings, Regex
- Techniques
  + What to do when Z3 fails to solve a problem
- Limitations
