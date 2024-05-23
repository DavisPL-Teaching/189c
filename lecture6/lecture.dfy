/*
  ===== Day 19 =====

  Introduction to Dafny!

  Last time:
  - We gave a high-level overview of formal verification and why it matters
    (when you might want to use it for a project)
  - We saw that many formal verification tools exist -- for different languages
    and purposes. In this class, we will use the Dafny verification language.
  - Key point: Dafny is both a programming language and a verification tool.

  Plan for today: jump into Dafny syntax and examples!

  Announcements: None!

  Misc:

  - Results of Hypothesis vs Z3 vote:
    Hypothesis: 12
    Z3: 27

  Questions?

  ===== Poll =====

  1. What is formal verification?
  2. Which of the following are the best reasons to use formal verification tools to prove that your code is correct?

  https://forms.gle/12rQLQfZZHUnmDBk6
  https://tinyurl.com/3srvuyt6

  ===== Resources =====

  This file is a modified version of the official Dafny tutorial:
  https://dafny-lang.github.io/dafny/OnlineTutorial/guide

  Thanks to Konstantinos Kallas for an earlier version of the file!
  That version (and a homework) can be found here:
  https://github.com/angelhof/penn-cis673-hw-dafny

  There are many additional resources about Dafny that are useful online.
  I often reference the reference manual:
  https://dafny.org/latest/DafnyRef/DafnyRef

  Rustan Leino, the creator of Dafny, also wrote an excellent textbook,
    *Program Proofs*
    https://mitpress.mit.edu/9780262546232/program-proofs/
  (if you can find a copy of it).

  Finally, there are some good PDF tutorials as well, such as
  (the slightly out of date):
  https://leino.science/papers/krml221.pdf
*/

// Here is the simple Dafny program that we introduced last time:

method Abs(x: int) returns (y: int)
  ensures y >= 0 // <-- specification! (postcondition)
{
  if x >= 0 {
    return x;
  } else {
    return -x;
  }
}

/*
  ===== Syntax =====

  Let's go over the syntax of the code above:

  - "Methods" are functions in standard languages.

    A method is something that you can execute.

    (Note: Dafny also has something called a function, which is a "pure function",
    we will see an example of that later.)

  - We have standard programming constructs (ifs, while loops, etc).

  - The input and output are typed!
    Values have specific types in Dafny.

  - We use `returns` above to indicate that the method returns a value;
    we can also return directly by setting the value y:

  - Dafny uses `:=` for assignment, and `==` for equality of values
    There is no single `=`.
*/

// Equivalent example
method Abs2(x: int) returns (y: int)
  ensures y >= 0
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

/*
  ===== Preconditions and postconditions =====

  We use `requires` to indicate a precondition, and
  `ensures` to indicate a postcondition.

  Last time, we saw that if we modify the code to do something wrong,
  Dafny will catch the error:
  - modifying ensures to a postcondition that is wrong?
  - modifying the return value to return -1 (e.g.)?
  - modifying requires to a precondition that is wrong?

  Summary: Dafny checks whether the spec holds:
  - for *all* inputs satisfying the precondition, after the program
    is run, the output satisfies the postcondition.

  Some design questions:

    Q: Why are return values (like y) named?

    - So that we can refer to them in the postcondition

    Q: Why are values (like x and y) typed?

    - Dafny needs to know the type of a value to be able to
      verify anything about it (and to convert it to a corresponding
      Z3 type).
*/

/*
  ===== Assume and assert =====

  Remember assume and assert?

  - We can use assumptions to tell Dafny we only care about
    executions that satisfy some condition.

  - We can also use assertions to tell Dafny to prove
    that some condition holds at a certain point in the code.

  As we learned with Hypothesis, preconditions and postconditions are
  just special cases of assumptions and assertions!

  What assumptions and assertions might we want to add to Abs?
*/

method Abs3(x: int) returns (y: int)
  ensures y >= 0
{
  if x >= 0 {
    y := x;
    // What assertion could we check here?
    assert y == x;
  } else {
    y := -x;
    // What assertion could we check here?
    assert y == -x;
    // What assumption + assertion could we add here?
    // assume x == -3;
    // assert y == 3;
    // What else?
    // assume x == -2;
    // assert false; // unreachable
    // ^ Assume is dangerous!
  }
}

// Once the code gets compiled, assume and assert statements go away
// in the final binary. That means that assume() statements are like
// cheating, and they are dangerous.

// Q: are integers bounded or unbounded?
// A: They are like in Python, they are unbounded.
//    Dafny does have a bounded int type as well.

// Methods can also have multiple return values, and multiple postconditions.
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y // Comment this out and see what happens!
  ensures less < x
  ensures x < more
{
  more := x + y;
  less := x - y;
  // comments: are not strictly necessary, of course!
}

/*
  Mini-exercise:

  Implement a Max function that returns the maximum of two integers,
  and write pre- and post-conditions for it.

  What kind of pre and postconditions would we like to have here?
*/

method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
  ensures c == a || c == b
  ensures c >= a
  ensures c >= b
{
  // fill in the code here
  // assume false; // remove this line when implemented
  if a <= b {
    c := b;
  } else {
    c := a;
  }
}

// Let's test to see if our method is working!

method TestMax()
{
  var a: int := 5; // The 'int' annotation is optional (it is inferred)
  var b: int := 50;
  var c := Max(a, b);
  assert c == 50;

  // Note that we've "tested" the code without actually running it!
  // We will circle back to that soon as well.
}

/*
  ===== Interfaces and abstraction =====

  The idea of preconditions/postconditions is a useful way to think about
  code in any programming language! But fundamentally, it is a form of
  abstraction:

  - Precondition: what does the method need to do its job?
  - Postcondition: what does the method guarantee to do when it's done?

  Fun fact: the idea of preconditions/postconditions is also known as
  "Design by Contract". The idea is that you can think of a method as
  a contract between the caller who wants something from the method, and the
  method, which provides that thing.

  There's a bit of a problem with Abs, though.
  To see what it is,
  in Dafny, let's see what happens when we try to use a test with Abs!
*/

method TestAbs()
{
  // What should we assert about Abs?

  var x: int := Abs(5);
  assert x >= 0;
  // Uncomment these lines, what happens?
  // var x := Abs(5);
  // assert x == 5;
}

/*
  Why didn't this work?

  This is because Dafny abstracts methods away by their pre and postconditions
  to simplify verification. This means that it doesn't look inside Abs' definition
  to verify the assertion, but rather uses the knowledge that it has of Abs' model.

  What's left of the method is only the pre and postconditions!

  This is a common scenario in formal verification: it often happens
  that the verifier doesn't have enough information to prove a property.
  And, we need to strengthen the model by making the postcondition stronger.

  What postconditions should we add to Abs to fix it?
*/

method AbsFixed(x: int) returns (y: int)
  // Fixed postcondition:
  ensures y >= 0
  ensures y == x || y == -x
  // The interface is complete! The contract fully specifies
  // what the output should be on every input.
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

method TestAbsFixed()
{
  var x := AbsFixed(5);
  assert x == 5;
}

/*
  However, our spec now describes exactly the body of the method, which is a bit redundant.

  That's what functions are for! We will see this next time.

  Recap:
  - We saw how to define basic methods (procedures) in Dafny
  - We saw the basic syntax for preconditions, postconditions,
    assume/assert, and how to write tests.
  - We will continue with more Dafny features next time!

  ##### Where we left off for Day 19 #####

  ===== Day 20 =====

  Announcements:

  - Dafny installation instructions:
    installation instructions on Windows/Linux/Codespaces
    are posted in the README.md
    (These will also be made available with HW4.)

  - HW4 release will be posted on Piazza when ready;
    you will have at least 2 weeks to complete once released.

  Plan:

  - Start with the poll

  - Continue with more Dafny concepts:
    + functions and expressions
    + running the code
    + strongest postconditions and weakest preconditions
    + recursion and loops

  Questions?

  ===== Poll =====

  Consider the following Double method:
*/

method Double(x: int) returns (y: int)
  // requires ... ensures ...
  // requires false // this function cannot be called
  // ensures false // this function never returns
  ensures y == x + x
{
  y := x + x;
}

// Which of the following pre/postconditions can we add
// to get both the method and the following test to pass?

method TestDouble()
{
  var x := Double(4);
  assert x == 8; // Uncomment this line
}

/*
  1. nothing (the test will pass as is)
  2. requires x == 5
  3. ensures y == 10
  4. ensures y == x + x
  5. requires x == 0 ensures y == x + x
  6. requires x == 5 ensures y == 10
  7. requires false
  8. ensures false
  9. requires (x == 5 ==> y == 10)
  10. ensures (x == 5 ==> y == 10)

  https://forms.gle/dV3uswiZnvz7BRdt7
  https://tinyurl.com/wk6fvfvm

  (After poll: try it out)
*/

/*
  ===== Functions =====

  Last time, we saw that we can't prove that Abs(5) == 5
  unless we give it a strong postcondition.
  This same problem occurs with options (1) and (2) above
  (Double(5) == 10):
  (Why?)

  The reason? *Abstraction:* A Dafny method is "opaque":
  considered abstracted by only its pre/postcondition behavior.

  There is an easier way:
  Dafny allows us to define mathematical functions
  that are not opaque when the Dafny verifier runs:
*/

function abs(x: int): int
{
  // Syntax looks a bit different: this is
  // mathematical expression syntax. Mathematical expressions
  // are also what appears in assert() statements and in pre/postconditions.
  if x >= 0 then x else -x
}

method TestAbsEasier()
{
  assert abs(5) == 5; // passes
  assert abs(-4) == 4; // passes
}

/*
  Functions expose another important concept in Dafny:
  only functions can be used in expressions!
  Methods cannot be used in expressions.

  (We ran into this problem last time!)

  What happens when we try to call AbsFixed(5) in an expression?
  What happens when we try to call abs(5) in an expression?
*/

method TestAbsExpression()
{
  var x := AbsFixed(5); // This is fine
  // assert AbsFixed(5) == 5; // Error
  assert x == 5; // This passes
  var y := abs(5); // This is fine
  assert abs(5) == 5; // This is fine
}

/*
  What's the reason for this?

  Functions represent mathematical functions: every time the function is called
  on the same input, it will return the same output.

  (If you've heard of the idea of "functional programming" or "pure functions",
  that's what functions in Dafny are like. There are whole languages dedicated to
  this, like Haskell.)

  Methods represent procedures: they can have side effects (something that happens
  when you run the function besides its input/output behavior), and can return different
  results on the same input (in theory).
  For example, it might have some state or mutate some variables.

  That means that it's not a valid thing to use in an assertion.
  Why?
  An assertion represents a statement that something is true about the state
  of your program at a given point in time.
  It would be very concerning if simply "evaluating" that assertion, changed
  whether or not it was true.

  Pragmatically speaking: you just have to remember that methods are different
  from functions and implemented separately, and only functions can be used
  in expressions.

  Recap:
  We've already learned the basics of verifying simple Dafny code!
  Methods (and tests), functions, expressions, preconditions, postconditions,
  and assert/assume.

  (One big thing missing: we haven't looked at loops or recursive functions!)

  Before we continue with more complex examples,
  I have a couple of digressions to make.
*/

/*
  ===== Digression 1: Running the code? =====

  You may have noticed something odd: we haven't run any code yet!
  In fact, even in our Tests, all we did was ask Dafny to verify that the test
  would pass.
  We only compiled the code, we didn't run it!

  But that doesn't mean Dafny can't run the code!

  Dafny is a *verification-aware* programming language.
  That means, it can verify your code, but it can also compile/run it!

  To run the code, we just need a Main() function:
*/

method Main()
{
  var x: int := -5; // Type annotation is optional
  var y: int := Abs(x);
  // assume x  == 0; // Uncomment to raise a warning about a bad assumption
  print "x = ", x, ", y = ", y, "\n";
}

/*
  To run from the command line, we can use the `dafny` command.
  Here are some of the options:

  1. `dafny verify lecture.dfy` -- to run the verifier only.
      This is equivalent to what we've been doing so far (checking the green
      bar on the left in VSCode).

  2. `dafny build lecture.dfy` -- to compile to a library, dafny.dll
     (This is also run by default with `dafny lecture.dfy`)
     We won't use this option much in this class.

  3. `dafny run lecture.dfy` -- to run the code!

  If we have warnings in the code, Dafny will refuse to compile the code;
  however, you can turn this off by adding the flag
    --allow-warnings
  You will get warnings if you use `assume` for example! (Why?)
  In general, it's best to remove all warnings before running the code.
*/

// Here's another example from the Dafny reference:
// datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)
// method Main()
// {
//   var x : Tree := Node(Node(Empty, 1, Empty), 2, Empty);
//   print "x=", x, "\n";
// }

/*
  There's also a fourth option to run Dafny!
  Perhaps you remember from last time, that one of the advantages of Dafny
  is that it can produce output in other languages, so it can integrate
  with your existing workflow.
  Try this:

  4. `dafny build --target:py lecture.dfy`

  This produces output in: lecture-py/module_.py.
  You can run the code with

  ```
  python3 __main__.py
  ```

  (You can ignore the other files.)
*/

/*
  ===== Digression 2: strongest postconditions and weakest preconditions =====

  We saw above that in order to prove properties about
  methods like Abs and Double,
  we needed to strengthen the postcondition to be stronger
  (or use a function instead of a method.)
  Is the new postcondition really as strong as it can be?

  Is ensures y == x + x really the strongest possible?

  We will see that the answer is yes: this is in a formal
  sense, the strongest possible statement about the output.

  On HW1, part 1B, you were asked to write specifications that are the
  *strongest possible* description of what the function does.
  What does that mean?

  Let's define:

  - Going forwards:
    Given a precondition,
    the *strongest postcondition* of a statement (or program) is the strongest property
    that is guaranteed to hold after executing the statement
    (assuming that the precondition holds)

  - Going backwards:
    Given the postcondition,
    the *weakest precondition* of a statement (or program) is the weakest condition
    that guarantees that the postcondition will hold after executing the statement.

  Here are some examples based on the Abs function;
  we will see more about this later!
*/

method StrongestPostconditionEx(x: int) returns (y: int)
  requires x >= 5
  // What ensures statement should go here?
  ensures y == abs(x + x)
  ensures y >= 10
  ensures x >= 5
{
  y := abs(x + x);
}

method WeakestPreconditionEx(x: int) returns (y: int)
  // What requires statement should go here?
  // requires false // Replace this line
  requires x >= 5 || x <= -5
  ensures y >= 10
{
  y := abs(x + x);
}

// ##### Where we left off for day 20 #####

/*
  ===== Day 21 =====

  Announcements:

  - HW4 is released! Due Monday, June 3
    https://classroom.github.com/a/YINeHx56
    https://github.com/DavisPL-Teaching/189c-hw4

  - **Dafny installation help office hours: Today 4pm**

    Installation instructions have been updated in the homework
    README file. An important note: you won't need the Dafny
    command line to complete the homework. You'll only need the
    Dafny VSCode extension (with the green bars on the side).

  - Looking ahead:
    **Class on Friday, May 31 will be via Zoom.**
    My office hours that week will be moved to Wednesday.
    (So leading up to the HW4 deadline you will have
    Wednesday, Friday, and Monday office hours.)

  Plan for today:

  - Poll
  - Finish strongest postconditions and weakest preconditions
  - Move on to Lecture 7: loop invariants!

  Questions?
*/

/*
  ===== Poll =====

  Consider the following method:

  method birthday(age: int) returns (new_age: int)
  {
    return age + 1;
  }

  1. If the precondition is
    age >= 0
  then what is the strongest postcondition?

  2. If the postcondition is
    new_age == age + 1 && new_age >= 0
  then what is the weakest precondition?

  https://forms.gle/9e7vf2zDae6FFDfD6
  https://tinyurl.com/3wfy9jjp
*/

method birthday(age: int) returns (new_age: int)
  // 1. SP(age >= 0)
  // requires age >= 0
  // ensures age >= 0 && new_age == age + 1
  // 2. WP(new_age == age + 1 && new_age >= 0)
  // requires age >= -1
  // ensures new_age == age + 1 && new_age >= 0
{
  return age + 1;
}

/*
  Another definition:
  StrongestPostcondition(P):
    Describe (the set of) all output states y such that
    running the method on an input state x satisfying
    P may produce output y

  WeakestPrecondition(Q):
    Describe (the set of) all input states x such that running
    the method on input x produces an output y satisfying Q

  The set of: just to emphasize there may be
  zero or more than one.

  input states/output states: we want to describe
  all variables in scope at input/output to the
  program, respectively.
  For the final: what variables are in scope
  will be mentioned.

  How do we actually compute these things?

  At every point in your program, write down exactly
  everything that is known to be true about the state of the program
  at that point.

  To do strongest postconditions: work forwards.
  To do weakest preconditions: work backwards.
*/

// What about this? (A harder one)
method StrongestPostconditionEx2(x: int) returns (y: int)
  requires x >= 5
  // TODO: what ensures statement should go here?
  // Let's figure it out!
  // What Dafny would do internally
  // ensures (
  //           (5 <= x <= 10 && y == 3 * x)
  //           ||
  //           (x > 10 && y == 2 * x)
  //         )
  // What we might come up with by hand
  ensures 5 <= x
  ensures (5 <= x <= 10) ==> y == 3 * x
  ensures (x > 10) ==> y == 2 * x
  // The two are equivalent.
{
  // What is true here?
  assert x >= 5;

  if x <= 10 {
    // What is true here?
    assert x >= 5 && x <= 10;

    y := abs(x +  x + x);

    // What is true here?
    assert x >= 5 && x <= 10 && y == abs(x + x + x);
    // Simplify (optional)
    assert 5 <= x <= 10 && y == x + x + x;

  } else {
    // What is true here?
    assert x >= 5 && x > 10;
    // Simplify (optional)
    assert x > 10;

    y := abs(x + x);

    // What is true here?
    assert x > 10 && y == abs(x + x);
    // Simplify
    assert x > 10 && y == x + x;

  }
  // What is true here?
  // What do we do at the end of an if block?
  assert (
      (5 <= x <= 10 && y == x + x + x)
      ||
      (x > 10 && y == x + x)
    );

  assert (
      (5 <= x <= 10 && y == 3 * x)
      ||
      (x > 10 && y == 2 * x)
    );

}

// The working backwords method!
method WeakestPreconditionEx2(x: int) returns (y: int)
  // TODO: uncomment
  ensures y >= 5
  // TODO: what requires statement should go here?
  // Let's figure it out!
  // What Dafny would come up with automatically
  requires (
             x <= 10 ==> abs(x + x + x) >= 5)
           &&
           (x > 10 ==> abs(x + x) >= 5
           )

{

  assert (
      (x <= 10 ==> abs(x + x + x) >= 5)
      &&
      (x > 10 ==> abs(x + x) >= 5)
    );

  if x <= 10 {
    assert abs(x + x + x) >= 5;

    y := abs(x +  x + x);

    assert y >= 5;
  } else {
    // Evaluate the assignment y := abs(x + x)
    // in reverse!
    assert abs(x + x) >= 5;

    y := abs(x + x);

    assert y >= 5;
  }
  assert y >= 5;
}

/*
  Strongest postconditions and weakest preconditions are a key part of how
  Dafny works internally -- it is calculating them implicitly all the time!

  The way it does it is basically the process we did above.
  It can be done in a completely routine way.

  This works great!
  But the problem with it?
  Loops and recursion.
  It doesn't work through loops and recursion -- and that leads
  us in to what we will see in Lecture 7.

  This process is also a super useful tool for debugging
  to see where the Dafny verifier is getting stuck.
*/
