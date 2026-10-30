method IndexOfMax(a: seq<int>) returns (best: nat)
  requires |a| > 0
  ensures best < |a| && forall j :: 0 <= j < |a| ==> a[j] <= a[best]
{
  best := 0;
  var k := 1;
  while k < |a|
    invariant 1 <= k <= |a| && best < |a|
    invariant forall j :: 0 <= j < k ==> a[j] <= a[best]
  {
    if a[k] > a[best]
       || (a[k] == a[best]
           && k % 2 == 0)
    {
      best := k;
    }
    k := k + 1;
  }
}

//::: Name - Condition atom that only breaks ties
//::: Description - The contract accepts any index of a maximum, so the tie-break atom can be replaced by any boolean: it is uncovered, while the atoms that keep a maximum are covered
//::: L7 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
//::: L13 - Uncovered
