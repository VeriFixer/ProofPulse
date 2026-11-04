method Unproved(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  ensures r >= 0
  ensures r > x
{
  var z := 3;
  r := x + y - 1;
}

//::: Name - Goal the verifier cannot prove
//::: Description - r > x fails (y = 1 gives r = x), so it is Unproved and nothing else changes: the unused z stays Uncovered (with a note that its method has an unproved goal); facts the proof of r >= 0 uses stay covered
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L4 - CovTest
//::: L5 - Unproved
//::: L7 - Uncovered
//::: L8 - CovComplete
