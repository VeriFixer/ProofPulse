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
//::: Description - The unsatisfiable precondition proves the postcondition alone, so precondition, postcondition and body are Vacuous
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - Vacuous
//::: L4 - Vacuous
//::: L5 - CovComplete
//::: L6 - Vacuous
//::: L7 - Vacuous
//::: L8 - Vacuous
