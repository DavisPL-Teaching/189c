/*
  A harder exercise:
  Implement a function that calculates
  pow(x, n) = x^n

  in a more efficient way than just multiplying x by itself n times.
*/

// Here is the easy recursive version.
// We want to write a more efficient version.
function pow(x: int, exp: nat): int
{
  if exp == 0 then 1 else x * pow(x, exp - 1)
}

// Lemmas
/* TODO: add lemmas here as needed */

method RepeatedSquare(x: int, exp: nat) returns (y: int)
  ensures y == pow(x, exp)
  // TODO: Uncomment to implement the function
  requires false
{
  // TODO
}
