method ret32(a: int) returns (x:int)
    ensures x==32 
{
    x := 32;
}

//::: Name - Basic code line cov complete
//::: Description - line 4 must appear code compelte as it is directly used to prove postcondition
//::: L1 - CovComplete
//::: L2 - CovTest
//::: L3 - CovComplete
//::: L4 - CovComplete