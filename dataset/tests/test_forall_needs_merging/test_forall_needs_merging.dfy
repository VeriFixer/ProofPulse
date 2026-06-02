method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    for i := 0 to |s|
        // invariant 0 <= i <= |s| // this is not needed on a for
        invariant |v| == i
        invariant forall k :: 0 <= k < i ==> v[k] == s[k]
    {
        v := v + [s[i]];
    }
}

//::: Name - Forall On proof pulse is having two condiiton
//::: Description - one containing ensuers .. and other with only after ensures
//::: they represent exactly the same but only one is being merged
//::: L3 - CovTest
