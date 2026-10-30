method ret32(a: int) returns (x:int)
    ensures x==32 
{
    x := 32;
}
method UseRet32() returns (y: int)
    ensures y == 32
{
	y := ret32(5);
}

//::: Name - Fully use postcondition
//::: Description - Postcondition fully needed: UseRet32 proves its own ensures from it
//::: L2 - CovComplete
