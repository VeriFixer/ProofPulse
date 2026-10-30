method ret32() returns (x:int)
    ensures x==32
{
    x := 32;
}

method Main(){
    var b := ret32();
    assert(b == 32);
}

method Twice() returns (y: int)
    ensures y == 64
{
    var b := ret32();
    y := b + b;
}

//::: Name - Postcondition complete as a caller needs it
//::: Description - Line 2 is CovComplete because Twice proves its own ensures from it (Main only tests it)
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L4 - CovComplete
//::: L8 - CovTest
//::: L9 - Uncovered