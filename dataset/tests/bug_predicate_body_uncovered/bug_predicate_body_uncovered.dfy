predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
    result := true;
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant result <==> forall k :: 0 <= k < i ==> (IsEven(k) ==> IsEven(lst[k]))
    {
        if IsEven(i) && !IsEven(lst[i])
        {
            result := false;
            break;
        }
    }
}

//::: Name - Predicate body should not block method coverage
//::: Description - The predicate body (line 3) is used opaquely by the prover. It should not cause the method to be classified as having uncovered body lines.
//::: L3 - CovComplete
//::: L7 - CovTest
//::: L9 - CovComplete
