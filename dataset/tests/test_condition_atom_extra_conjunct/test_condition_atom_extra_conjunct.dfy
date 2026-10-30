method Find(a: seq<int>, x: int) returns (i: int)
  requires x in a
  ensures 0 <= i < |a| && a[i] == x
{
  i := 0;
  while !(a[i] == x)
    invariant 0 <= i < |a| && x in a[i..]
    decreases |a| - i
  {
    i := i + 1;
  }
  if i + 1 < |a|
     && a[i + 1] == x
     && i % 3 == 0
  {
    i := i + 1;
  }
}

//::: Name - One unused conjunct of a condition
//::: Description - Moving to the next occurrence of x needs the bound and the value test, but not the extra conjunct, which only decides which occurrence is returned
//::: L6 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
//::: L14 - Uncovered
