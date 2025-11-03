method swap(a : int, b:int) returns (c:int, d:int)
    ensures a + 1 == c
    ensures b + 1 == d
{
    c,d := a + 1,b + 1; // line appears uncovered but if split in two assigment it is covered
}

//::: Name - Two assigments same line bug
//::: Description - Line appears uncovered, but if assigment separated in two it works
//::: L5 - CovComplete