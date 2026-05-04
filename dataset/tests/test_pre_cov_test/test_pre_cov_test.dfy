method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := 32 + 1;
}

method Main(){
    var b := ret32(32);
}

//::: Name - Precondition not necessary for method to be correct, but is used in checking the calls for that method
//::: Description - Line 2 should be CovComplete
//::: L1 - CovComplete
//::: L2 - CovTest
//::: L3 - CovTest
//::: L4 - CovComplete
//::: L5 - CovComplete