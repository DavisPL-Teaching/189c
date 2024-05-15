/*
  This is an example of a much more complex Dafny program.

  We may get to it in a future lecture.
*/

function power(x: int, pow: nat): int
  // ensures power(x * x, pow) == power(x, pow) * power(x, pow)
  // decreases pow
{
  if pow == 0 then 1 else x * power(x, pow - 1)
}

lemma PowerProduct()
  ensures forall x: int, y: int, pow: nat {:induction pow} :: power(x * y, pow) == power(x, pow) * power(y, pow)
{}

lemma PowerInc()
  ensures forall x: int, pow1: nat {:induction pow1} :: power(x, pow1 + 1) == power(x, pow1) * x
{}

lemma PowerSumInstance(pow1: nat, pow2: nat)
  ensures forall x: int :: power(x, pow1 + pow2) == power(x, pow1) * power(x, pow2)
{
  if pow2 == 0 {
  } else if pow2 == 1 {
    PowerInc();
  } else {
    PowerSumInstance(pow1, pow2 - 1);
  }
}

lemma PowerProdInstance(pow: nat)
  ensures forall x1: int, x2: int :: power(x1, pow) * power(x2, pow) == power(x1 * x2, pow)
{
  PowerProduct();
}

// TODO: Can we prove the general version?
// lemma PowerSum()
//   ensures forall x: int, pow1: nat, pow2: nat :: power(x, pow1 + pow2) == power(x, pow1) * power(x, pow2)
// {
//   PowerSumInstance();
// }

// lemma PowerPower()
//   ensures forall x: int, y: int, pow1: nat, pow2: nat {:induction pow2} ::
//             power(power(x, pow1), pow2) == power(x, pow1 * pow2)
// {}

method RepeatedSquare(x: int, pow: nat) returns (y: int)
  ensures y == power(x, pow)
{
  var result := 1;
  var square := x;
  var remaining := pow;
  assert result * power(square, remaining) == power(x, pow);
  while remaining > 0
    invariant result * power(square, remaining) == power(x, pow)
  {
    ghost var remaining_half := remaining / 2;
    ghost var remaining_rem := remaining % 2;
    assert remaining == remaining_half * 2 + remaining_rem;
    if remaining % 2 == 1 {
      result := result * square;
      assert result * power(square, remaining) == power(x, pow) * square;
    }
    assert result * power(square, remaining) == power(x, pow) * power(square, remaining_rem);
    assert result * power(square, 2 * remaining_half + remaining_rem) == power(x, pow) * power(square, remaining_rem);
    assert result * power(square, 2 * remaining_half) * power(square, remaining_rem) == power(x, pow) * power(square, remaining_rem);
    assert result * power(square, 2 * remaining_half) == power(x, pow);
    assert result * power(square, remaining_half + remaining_half) == power(x, pow);

    // (!)
    PowerSumInstance(remaining_half, remaining_half);
    assert result * power(square, remaining_half) * power(square, remaining_half) == power(x, pow);
    PowerProdInstance(remaining_half);
    assert result * power(square * square, remaining_half) == power(x, pow);

    // The rest is easy
    assert result * power(square * square, remaining / 2) == power(x, pow);
    square := square * square;
    assert result * power(square, remaining / 2) == power(x, pow);
    remaining := remaining / 2;
  }
  y := result;
}
