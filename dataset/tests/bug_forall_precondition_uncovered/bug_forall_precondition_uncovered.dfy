method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{
    result := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == a[k] / b[k]
    {
        result := result + [a[i] / b[i]];
    }
}

//::: Name - Quantified precondition should be covered
//::: Description - requires forall i :: ... b[i] != 0 guards against division by zero and is used by the prover via quantifier instantiation, but appears Uncovered
//::: L2 - CovComplete
//::: L3 - CovComplete
