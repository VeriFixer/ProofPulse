method swap(a : int, b:int) returns (c:int, d:int)
    ensures a + 1 == c
    ensures b + 1 == d
{
    c,d := a + 1,b + 1; //:: 2 of this lines _two_assigments_same_line.dfy(5,5)-(5,15): assignment (or return)
}

//:: Not sure what causes this bug need to debug however I can simple not support
//:: double assigments on this way (But need to check)
//:: Can simply not supported it in Coverage

method swap1(a : int, b:int) returns (c:int, d:int)
    ensures a + 1 == c
    ensures b + 1 == d
{
    c := a + 1; //:: No problem like so
    d := b + 1;
}
