method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := a+1;
}

//::: Name - Precondition is necessary in order for the postcondition to hold
//::: Description - Line 2 should be CovComplete
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovTest
//::: L4 - CovComplete
//::: L5 - CovComplete