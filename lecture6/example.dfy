/*
    Simple Dafny program

    (To check your installation)

    Feature:
    No need to rewrite the function!

    Both the program and the spec are in the
    same file.
*/

method Abs(x: int) returns (y: int)
  requires true
  ensures y >= 0
  ensures y == x || y == -x
{
  if x >= 0 {
    return x;
  } else {
    return -x;
  }
}
