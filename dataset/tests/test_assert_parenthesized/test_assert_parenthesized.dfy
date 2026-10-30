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

//::: Name - Parenthesized assert used by a postcondition
//::: Description - Dafny reports the use as an assert statement whose range includes the parentheses; the assertion inside it must be covered
//::: L18 - CovComplete
