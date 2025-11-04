method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := 32 + 1;
}

//::: Name - Precondition not necessary for method to be correct, and for now is not being necessary in checking any call of the method
//::: Description - Line 2 should be CovComplete
//::: L1 - CovComplete
//::: L2 - Uncovered
//::: L3 - CovTest
//::: L4 - CovComplete
//::: L5 - CovComplete