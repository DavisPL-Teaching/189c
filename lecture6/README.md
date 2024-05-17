# Lecture 6: Formal Verification

(Day 18 and the following days)

This lecture begins the second half of the course!

To follow along:
- `lecture6/README.md`
- `lecture6/Slides.pdf`
- [Repo](https://github.com/DavisPL-Teaching/189C/)

We will start with some general motivational slides.
Then, we will continue with this file.

(Switch to slides)

## Summary from the slides

We know about:
- Writing code
- Writing specifications (Hypothesis and Z3)
- Proving specifications correct (Z3)

### What is formal verification?

Combination of all of the above!

## Poll link (if you missed it)

https://forms.gle/MashpCJkwJc64teNA
https://tinyurl.com/49vatd6f

### Why use formal verification?

Answer:
Formal verification is especially useful in cases where:
- **Correctness is critical**: if the software fails, some very
  serious consequence will occur
- **Security**: if the software is vulnerable to attack, you may
  not have considered all the ways it could be exploited
- **A bug is very expensive or catastrophic** for your
  company/organization

### Examples

(These were covered in the slides)

- Pentium FDIV bug: affected Intel Pentium processors in 1994.

  + recall of all defective Intel processors at the time
  + $475 million in losses!

- Therac-25: one of the most (in)famous software bugs in history.

  + radiation therapy machine (1985-1987)
  + Under seemingly random conditions it would give 100+x the intended
    radiation dose to patients, manufacturers repeatedly denied it
    was
  + 6 incidents of overdose, 3 deaths, 3 serious injuries

  + Not verified! Would verification have caught this bug?
    (One can hope)

- Low-level cryptographic libraries

  + if these are incorrect, it can take down the whole security foundation of the internet!

  + Signal messaging app: verification effort for core messaging protocol going back to 2017

  + AWS-LibCrypto: open source SSL/OpenSSL implementaiton that is proved
    using Coq, HOLLight, and other tools.
    [report](https://sos-vo.org/node/107141)

  + To cite another misc. example:
    Galois, inc. has several projects in this area including the
    [SAW](https://saw.galois.com/) verification tools and the
    [Cryptol](https://cryptol.net/) domain-specific language

- Access control bugs

  + Expose critical customer or user data to malicious actors!

  + One failure would be enough to destroy trust in an entire cloud
    provider

  + AWS is investing millions in verification tools (including using Z3 and Dafny) for AWS S3 and IAM, AWS Encryption SDK, and other
    projects

- Blockchain technology -- lots of startups, e.g.

  + [Cubist](https://cubist.dev/about) key management technology

  + [Veridise](https://veridise.org/) blockchain verification tools

## Approaches to verification

Most of this part was not covered in the slides, but may be of general interest to some of you!

### Why Dafny?

- It's modern (actively developed)
- It's used in real industry applications (Microsoft, Amazon)
- It can *cross-compile* to other languages: such as C#, Go, Python, Java, and JavaScript.
- It has a good IDE (VSCode extension)

### Verification tools for popular programming languages

- [CMBC](https://www.cprover.org/cbmc/) for C and C++
  [CPROVER manual](https://www.cprover.org/cprover-manual/)

  C and C++ have the C Bounded Model Checker (CMBC) / CPROVER framework,
  which is widely used and deployed in practice to verify real low-level systems code,
  for example at Amazon.

  And others: [Verifast](https://github.com/verifast/verifast)

- For Python: [Deal](https://deal.readthedocs.io/basic/verification.html)
  is a precondition/postcondition framework for Python, with an experimental
  verifier built in.

- For Rust:
  [Flux](https://github.com/flux-rs/flux),
  [Verus](https://github.com/verus-lang/verus),
  [Prusti](https://github.com/viperproject/prusti-dev),
  and [Creusot](https://github.com/creusot-rs/creusot)

- [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell/) for Haskell

- [KeY](https://www.key-project.org/) for Java

    Also: [JBMC](https://www.cprover.org/jbmc/), [JayHorn](https://github.com/jayhorn/jayhorn) and others

- Others:
    [KJS](https://github.com/kframework/javascript-semantics)
    formal semantics and verifier for JavaScript
    Experimental verifiers for [TypeScript](https://formal.land/docs/verification/typescript)
    and many others

- If you don't see your favorite programming language here, write your own! :)

### A different approach (that Dafny uses)

A different appraoch is to separate the verification into two steps:

1. Verification in the verification programming language

2. Extraction to produce code in a target language

For example:
- [Coq](https://coq.inria.fr/) can be extracted to OCaml code
- [Agda](https://agda.readthedocs.io/en/v2.5.2/tools/compilers.html) can be extracted to Haskell code
- [Dafny](https://dafny.org/) can be transpiled to C#, Go, Python, Java, and JavaScript

Main idea: only write the code once and verify it within the same system!
Then integrate the transpiled code with your existing libraries
and workflow.

## Getting started: installing Dafny

You will need to have Dafny installed.

- If you are on Mac, see [Homework 0](https://github.com/DavisPL-Teaching/189c-hw0) for instructions:
  ```
  brew install dotnet
  brew install dafny
  ```
  Then, in VSCode, install the Dafny extension -- link here:
  https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode

- On Windows or on GitHub Codespaces:
  In VSCode, install the Dafny extension (link above).
  Open up a Dafny file and wait for the extension to prompt
  you to confirm Dafny 4.6.0.

  Make sure that the green checkmarks are showing up in VSCode before
  continuing!

  **Note:** I have had some trouble running Codespaces on Firefox,
  so if you get an "unable to connect" error try using a different
  browser, like Safari or Chrome.

  Then, to run Dafny from the command line, you just need to add
  `dafny` to your PATH. Here's how to do that:

  You should see in the Dafny output the path to where `dafny`
  is installed, like this:
  ```
  extracting Dafny to /home/codespace/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github
  ```
  You can also find the path to Dafny directly by doing:
  ```
  find /home -type f -name dafny
  ```
  On Windows, you should be able to run these in a linux/bash terminal if you have WSL.
  Although Powershell is not recommended, here is the Powershell equivalent:
  ```
  Get-ChildItem -Recurse | Where-Object { $_.Name -like "Dafny.exe" }
  ```

  If none of those worked, try the (more exhaustive but will take much longer to run)
  ```
  find / -type f -name dafny 2>/dev/null
  ```

  Then, add that path to your PATH, **without** the last `dafny` at the end. For example, if the path is
  `home/vscode/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github/dafny/dafny`:
  ```
  export PATH=$PATH:/home/vscode/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github/dafny
  ```

  That's it! Now `dafny` should work from the command line.
  See "Checking that the installation worked" below.

- On Linux: the instructions should be the same as
  for GitHub Codespaces.
  Before running the VSCode extension, you may need to
  run `sudo apt install dotnet-sdk-6.0` to make sure dotnet is installed.
  As with Windows, install VSCode and the VSCode extension using
  the link above.
  Make sure that the green checkmarks are showing up in VSCode
  first before trying to get `dafny` to work on the command line
  (by adding it to your PATH).
  That's it!

**Checking that installation worked:**
Check that the green checkmarks are showing up on the side in VSCode.
If they are not, you may need to refresh the file or restart VSCode.

For the command line, run `dafny --version`, you should get something like:
```
4.6.0
```
or:
```
4.6.0+7c82175da631d3fdc3acea92a3614d66a3fdf7f2
```
You can also run `dafny run file.dfy` on a particular file `file.dfy`
and Dafny should verify and run the file.

If the green checkmarks work but the command line doesn't, that probably means you haven't added Dafny to your PATH yet
(see the Windows/Codespaces instructions).

**Troubleshooting:**
If you are having any trouble after following the installation instructions above,
please let us know by making a post on Piazza and we will try to help
you! See
[this post](https://piazza.com/class/lt90i40zrot3ue/post/28)
for Piazza guidelines about posting errors.
If the instructions are not working locally on your machine,
try running Dafny in a codespace via the instructions above.

## Resources

- [Dafny](https://dafny.org/)
- [Reference manual and user guide](https://dafny.org/latest/DafnyRef/DafnyRef)
- Textbook: *Program Proofs,* by Rustan M. Leino -- [link](https://mitpress.mit.edu/9780262546232/program-proofs/)
