method Zeros(n: array<int>) returns (ex: array<int>)
  ensures n.Length == ex.Length
  ensures forall i: int :: 0 <= i < n.Length ==> ex[i] == 0
{
  var z := 0;      // irrelevant
  ex := new int[n.Length];
  var i := 0;
  while i < n.Length
    invariant 0 <= i <= n.Length
    invariant forall k: int :: 0 <= k < i ==> ex[k] == 0
  {
    ex[i] := 0;
    i := i + 1;
  }
}

//::: Name - Irrelevant local variable next to a loop proof
//::: Description - the unused local z stays uncovered; the loop invariants and the loop body are needed for the postconditions
//::: L5 - Uncovered
//::: L6 - CovComplete
//::: L7 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
