"""
Optimizing compiler using Z3

This was an optional extra credit problem on HW2 from a previous
iteration of the course.
It is provided here just for those curious.

=== Intro ===

This part explores an example application of Z3.
Your goal is to use Z3 to write a small interpreter
and optimizer for a minimal programming language.

=== Terminology ===

Some terminology used in this problem:
- A "parser" reads in a program source code and turns
it into an internal data structure representing the program.
- An "interpreter" executes this program, usually one line at a time.
- An "optimizer" takes the program and tries to make it more
efficient to execute.

We don't have a full compiler here because we won't be
producing machine code, but the idea is roughly the same.
To make a compiler, you would just need to add an extra step
to convert the internal data structure into machine code like
assembly or LLVM IR.

=== Input ===

The input to your program is a list of one-line commands.
Each of the lines is one of the following:

    X := val
    Set the varaible X to the value "val" (a plain integer).

    X := Y
    Set the variable X to the value of the variable Y.

    X := Y + Z
    Set the variable X to the sum of the variables Y and Z.

    X := Y * Z
    Set the variable X to the product of the variables Y and Z.

    IF X >= Y THEN
    Start of an if block: compares two variables X and Y
    for equality.

    ELSE
    Start of an else block.

    END IF
    End of an if block.

    INPUT X
    Read an integer from the user and store it in X.

    OUTPUT X
    Print the value of X.

In this language, a variable (X) can be any single-character capital string.

=== Executing commands ===

To execute commands, you should interpret them as follows:
at any point in time, each variable has an integer value.
If variables are not initialized, they are assumed to be 0.
Each command is interpreted in order from top to bottom,
and is run by modifying the values of each variable.

=== Example Program ===

Here is an example program to add the number X and the number Y
from the user.

    INPUT X
    INPUT Y
    Z := X + Y
    OUTPUT Z

And here is the absolute value function:

    INPUT X
    IF X >= 0 THEN
        Y := X
    ELSE
        Z := -1
        Y := Z * X
    END IF
    OUTPUT Y

=== Task 1: Parser ===

Your first step is to write a parser that takes a list of
commands from a file and converts them into a list of
commands that can be executed by your interpreter.

It may be helpful to store additional information about
each command: what type of command it is, and if it is an IF
statement, the index of the corresponding ELSE or END IF statements.

=== Task 2: Interpreter ===

For the interpreter, take your list of commands and execute them.
You should be able to handle nested IF statements
and remember to handle input (from the user) and output (printing
out to the console).

=== Task 3: Optimizer ===

Finally, write an optimizer that takes a list of commands and
removes any specific IF or ELSE blocks that are not necessary.
This can be run prior to the interpreter.

This specific optimization is called "dead code elimination"
and is a common optimization used in compilers.
Here is an outline of how to do this:

- Write a function that associates each line of the program
  with a Z3 expression for each variable. It should describe
  the value of the variable as a function of any input variables
  that were accumulated along the way.

- For each IF block, use Z3 to check if either the IF
  or the ELSE blocks can be removed.
  If so, remove the block and update the program.

  For example, if the check is X >= Y, and Z3 can prove
  that X >= Y is always true (given the expressions for X and Y),
  then the ELSE block can be removed.

You may need to be careful about handling input.
For a line X := input, you will need to add a new variable
to your Z3 expression that represents the input and ensure
that all these variables are distinct.

=== Task 4: Test Input ===

Test your program by running it on the following input:

    INPUT X
    IF X >= 0 THEN
        Y := X
    ELSE
        Z := -1
        Y := Z * X
    END IF
    IF Y < 0 THEN
        Z := 0
        OUTPUT Z
    ELSE
        OUTPUT Y
    END IF

Because Y is always >= 0, the second IF block is dead code
and should be eliminated by your optimizer.

You can also check that running the original program gives the
same result as running the optimized program.
"""
