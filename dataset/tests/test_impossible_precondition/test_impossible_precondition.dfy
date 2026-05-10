method DemoImpossiblePrecondition(a: int)
    returns (r: int)
  requires forall t :: t*t + 1 <= t*t
  ensures 2 == 3
{
  var k := a + 1;
  var m := k * 2;
  r := m - k;
}

//::: Name - Impossible precondition makes postcondition vacuously true
//::: Description - When precondition is unsatisfiable, postcondition is CovComplete (!) and body is Uncovered
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L4 - CovTest
//::: L5 - CovComplete
//::: L6 - Uncovered
//::: L7 - Uncovered
//::: L8 - Uncovered
