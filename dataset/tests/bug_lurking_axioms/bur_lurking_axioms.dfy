method zeroVector(n : array<int>) returns (ex:array<int>)
    ensures n.Length == ex.Length
    ensures forall i:int :: 0<= i < n.Length ==> ex[i] == 0
{
    var z:= 0;
    ex := new int[n.Length];
    var i := 0;
    while(i < n.Length)
        invariant 0 <= i <= n.Length
        invariant forall k:int :: 0<= k < i ==> ex[k] == 0
    {
        ex[i] := 0;
        i := i + 1;
    }
}
// L3 proably is showing lirking axiom bug Is appearing as Uncovered
// But should be covTest

//::: Name - Checking Lurking Axioms
//::: Description - Uncovered lurking Axiom it seems (does not appears in proof dependencies)
//::: L3 - CovTest