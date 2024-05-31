/*
    Lecture 8: Safety properties
    + Introduction to Rust

    This is a Rust file! (.rs)

    Rust syntax is similar to C/C++, but it has stricter
    rules for things like type annotations, mutability, and
    pointers.
    It is also strongly influenced by languages like Haskell
    and OCaml.

    To get started using Rust on your machine,
    copy and paste the command from the Rust website:
    https://www.rust-lang.org/
    Further instructions are found in HW5:
    https://github.com/DavisPL-Teaching/189c-hw5-optional/

    Rust files are managed with Cargo.

        cargo run
        cargo test

    We're in the src/ directory, where all Rust files go.
*/

/*
    ===== Safety properties =====

    So far, specs we have considered come in the following forms:

    - Pre/postconditions
    - Assume and assert statements
    - Termination (a bit -- have not covered in detail)

    Here's our example abs() function that we have seen before.
    Rust doesn't directly have pre/postconditions, but we can use
    an assert statement to illustrate the idea.
*/

fn abs(x: i64) -> i64 {
    if x < 0 {
        // As with Dafny functions, return is optional.
        // By default, the last line in an expression block
        // is the return value.
        // This is mostly just for convenience and style.
        -x
    } else {
        x
    }
}

fn abs_spec(x: i64) -> bool {
    // Call the function
    let result = abs(x);
    // Return the postcondition
    result >= 0 && (result == x || result == -x)
}

// Here's how to write a unit test
// Uncomment to run
// #[test]
fn test_abs() {
    assert!(abs_spec(-5));
    assert!(abs_spec(0));
    assert!(abs_spec(5));
}

// Run with: cargo test

/*
    But these are actually quite limited. There are many properties
    that go beyond assume and assert.
    For example:

    - The program never access invalid memory
    - The program does not connect to the internet
    - The program never constructs an invalid value of type `bool`
    (i.e., a boolean that is not 0 or 1)

    Important exercise:
    Why are these properties not specifiable as
    pre/postconditions or using assert statements?
*/

// Uncomment to run
// #[test]
fn test_program_never_accesses_invalid_memory() {
    let x = -10;
    let result = abs(x);
    // Test that abs did not access invalid memory
    // Does this work?
    unimplemented!();
}

/*
    What is a safety property?

    All of the above are examples of safety properties.

    Recall: a spec is a true or false property about a program.

    - A **safety property** is a spec of the following form:
    when the program is run, a bad thing never occurs.

    Q: What is a "bad thing"?
    A: It can be anything. The point of a safety
    property is that there are some set of bad events that
    could occur, say X, and the safety property says that
    X never happens.

    Not just at the time the program has input or produces output --
    at any point during the execution of the program!
*/

// Uncomment to run
// #[test]
// #[should_panic]
#[allow(clippy::useless_vec)]
fn example_invalid_memory() {
    let mut v = vec![1, 2, 3];
    // This is a bug! We are accessing memory that is not allocated.
    v[10] = 5;
}

/*
    ===== Safety properties we are interested in =====

    We will focus on the following three important classes of safety
    properties:

    - **Type safety:** A value of a type T is always a valid value of
    that type, never some other value.
    Example: bool, always 0 or 1 (not some other int)
    example: int, always a value betweeen -2^31 and 2^31 - 1
    Example: Vec<int>, always consists of a length and a pointer
        to some values of type int

    Q: Can we rewrite our abs function to take advantage
    of type safety?
*/

fn abs_typed(x: i64) -> u64 {
    // TODO
    unimplemented!();
}

// Q: How does this differ from the previous abs function?

// Note: This may not be so surprising in this simple case,
// but in more complex programs, type safety can be a very
// powerful tool for ensuring the safety of your code.

/*
    Two other kinds of safety properties that Rust
    cares about:

    - **Memory safety:** Roughly speaking: memory accesses are always
    valid. This includes:
        - the program only reads from valid, properly allocated memory
        - the program only writes to valid, properly allocated memory
        - the program does not free the same memory twice
        - the program does not crash with a segmentation fault
    Also sometimes included:
        - if memory is allocated, then that memory is later freed
        (no memory leaks)

    One other that is important for Rust, but which we will not discuss
    is related to concurrent programs:

    - **Data race freedom:** It never happens that two threads try
    to write to the same memory location at the same time.
    (Or, one thread tries to write and one thread tries to read.)
*/

/*
    ===== So, what is Rust, anyway? =====

    Rust is a very fast language (performance typically
    comparable to that of C -- sometimes better)
    that enforces type safety, memory safety, and data race freedom.

    That means: if you write any program in Rust
    (excluding using some explicitly unsafe features, like the
    `unsafe` keyword),
    it is guaranteed to satisfy these safety properties.

    For a detailed introduction, feel free to check out the slides
    for my Rust course at UPenn:

    https://github.com/upenn-cis198/lecture1/blob/master/lecture1_slides_public.pdf

    And the Rust book (interactive version):

    https://rust-book.cs.brown.edu/

    You can also read the Wikipedia page:

    https://en.wikipedia.org/wiki/Rust_(programming_language)

    ===== Other specifications? =====

    Fun fact: There are even more advanced properties than
    safety properties. For example:

    - If the program is run twice on different inputs,
      the running time is the same
    (this is called constant-time programming, it is very
    important for some security and cryptography applications)

    - If the program is run twice on the same input, the
      output is the same
      (this is called determinism)

    And many others.
    We won't cover more advanced properties like these in
    this class.
*/
