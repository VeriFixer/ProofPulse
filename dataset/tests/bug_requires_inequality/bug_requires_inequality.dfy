method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{
    firstPart := arr[..L];
    secondPart := arr[L..];
}

//::: Name - Predicate body should not block method coverage
//::: Description - The predicate body (line 3) is used opaquely by the prover. It should not cause the method to be classified as having uncovered body lines.
//::: L2 - CovComplete
