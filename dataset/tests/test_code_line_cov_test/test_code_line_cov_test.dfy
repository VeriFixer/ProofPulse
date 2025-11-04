method ret32(a: int) returns (x:int)
{
    x := 32;
    assert(x == 32);
}

//::: Name - Basic code line cov test
//::: Description - line 3 should appear covTest, has it is not used to prove any postcondition but an assertion
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovTest