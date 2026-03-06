/*
    An activity / extended exercise.

    WQ26: We did not get to this activity in class this year!
    But you may find it fun to try on your own time.

    If you get stuck, see repeated-squares-solution for the solution.

    ===== Activity today =====

    Work on a harder exercise (as much as we can get through):
    Implement a function that calculates

        pow(x, n) = x^n

    (E.g. pow(3, 2) == 9, exponent function from basic arithmetic.)

    in a more efficient way than just multiplying x by itself n times.

    Similar approach to examples we've seen before:
    - Define a function version that is "obviously" correct
    - Write a more complicated algorithm, and prove that it's equivalent
        to the function version.
*/

// Here is the easy recursive version.
// We want to write a more efficient version.
function pow(x: int, exp: nat): int
{
    if exp == 0 then 1 else x * pow(x, exp - 1)
}
