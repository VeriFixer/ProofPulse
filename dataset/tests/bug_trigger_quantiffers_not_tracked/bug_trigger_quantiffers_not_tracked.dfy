predicate IsSublistAt(sub: seq<int>, main: seq<int>, i: int) {
    0 <= i <= |main| - |sub| && sub == main[i .. i + |sub|]
}

method IsSublist ( sub : seq < int > , main : seq < int >) returns ( result : bool )
    ensures result == exists k  :: IsSublistAt(sub, main, k)
{
    if | sub | > | main | {
        return false ;
    }
    
    result := false ;

    for i := 0 to |main| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !IsSublistAt(sub, main, j)
    {
        if sub == main[i .. i + |sub|] {
            assert(IsSublistAt(sub,main,i));
            return true;
        }
    }

    result := false ;
}

//::: Name - Quantifers trigger not tracked
//::: Description - Some great finds (13,77) and some bugs
//::: L18 - CovComplete
