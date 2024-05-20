/*
  A harder exercise:
  Implement a function that calculates
  pow(x, n) = x^n

  in a more efficient way than just multiplying x by itself n times.
*/

// Here is the easy recursive version.
// We want to write a more efficient version.
function power(x: int, pow: nat): int
{
  if pow == 0 then 1 else x * power(x, pow - 1)
}

// Lemmas
/* TODO: add lemmas here as needed */

method RepeatedSquare(x: int, pow: nat) returns (y: int)
  ensures y == power(x, pow)
  // TODO: Uncomment to implement the function
  requires false
{
  // TODO
}
