/*
    Simple Dafny program

    (To check your installation)
*/

method Abs(x: int) returns (y: int)
  requires x >= 0
  ensures y >= 0
{
  if x >= 0 {
    return x;
  } else {
    return -x;
  }
}
