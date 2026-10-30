// The contract does not fix the sign of r, so the test of x is unused.
method Abs(x: int) returns (r: int)
  ensures r * r == x * x
{
  if x < 0 {
    r := -x;
  } else {
    r := x;
  }
}

// Same code with the sign fixed: the test is needed.
method AbsFull(x: int) returns (r: int)
  ensures r >= 0 && r * r == x * x
{
  if x < 0 {
    r := -x;
  } else {
    r := x;
  }
}

//::: Name - Condition atom unused under a weak contract
//::: Description - A condition that decides the output but that the proof never relies on points at a missing postcondition; once the contract fixes the sign, the same atom is covered
//::: L5 - Uncovered
//::: L16 - CovComplete
