method ret32(a: int) returns (x:int)
{
    x := 32;
    assert(x == 32);
}

//::: Name - Basic code line cov complete
//::: Description - line 4 must appear code compelte as it is directly used to prove postcondition
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovTest
//::: L4 - CovTest