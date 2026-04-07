method ret32(a: int) returns (x:int)
    ensures x==32 
{
    x := 32;
}
method Main() {
	var n := ret32(5);
    assert n==32;
}

//::: Name - Fully use postcondition
//::: Description - Postcondition fully needed for main use
//::: L2 - CovComplete
