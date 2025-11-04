method ret32() returns (x:int)
    ensures 3==3
{
    x := 32;
}

//::: Name - Postcondition complete as it is used on Main
//::: Description - Line 2 should be CovComplete as it is used on Main
//::: L1 - CovComplete
//::: L2 - Uncovered
//::: L3 - CovComplete
//::: L4 - Uncovered