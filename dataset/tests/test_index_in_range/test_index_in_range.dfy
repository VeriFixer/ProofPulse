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
// Line 9 is cov test as it is only needed for the automatic assertion ex[k] in range on line 10
// and as none are signalled as directly needed for the outer proof it appears as covTest.
// L2 is complete as L2 is necessary fir ensureing correctness of second ensure!

// L3 proably is showing lirking axiom bug Is appearing as Uncovered
// L6 is the assigment bug but with news that already was reported So it appears Uncovered

//::: Name - Checking indexes assertions, probably should modify behaviour
//::: Description - Simple Zero Vector creation to test index accesses
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - Uncovered
//::: L4 - CovComplete
//::: L5 - CovComplete
//::: L6 - Uncovered
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovTest
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
//::: L14 - CovComplete