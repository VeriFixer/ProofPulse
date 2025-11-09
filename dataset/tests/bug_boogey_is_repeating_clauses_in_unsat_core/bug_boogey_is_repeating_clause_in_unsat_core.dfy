method zeroVector(n : array<int>) returns (ex:array<int>)
    ensures n.Length == ex.Length
    ensures forall i:int :: 0<= i < n.Length ==> ex[i] == 0
{
    //var z:= 0;
    ex := new int[n.Length];
    var i := 0;
    while(i < n.Length)
        invariant 0 <= i <= n.Length
        invariant forall k:int :: 0<= k < i ==> ex[k] == 0
    {
        ex[i] := 0;
        i := i + 1;
    }
}
// L5 appears covered, The problem is that with that line the following proof oligations are created
//  Assertion batch 12:
//    Outcome: Valid
//    Duration: 00:00:00.1505889
//    Resource count: 15494
    
//    Assertions:
//      test_index_in_range.dfy(9,21): this loop invariant is maintained by the loop
 
//    Proof dependencies:
//      test_index_in_range.dfy(5,9)-(5,14): assignment (or return)
//      test_index_in_range.dfy(9,19)-(9,24): loop invariant always holds
//      test_index_in_range.dfy(13,9)-(13,19): assignment (or return)

// Core by smt solver dies not seem that it was minimize.

// But the problem gets weirder if we comment out that line commenting out we obtain
// Assertion batch 12:
//    Outcome: Valid
//    Duration: 00:00:00.1301369
//    Resource count: 15416

//    Assertions:
//      test_index_in_range.dfy(9,21): this loop invariant is maintained by the loop

//    Proof dependencies:
//      test_index_in_range.dfy(9,19)-(9,24): loop invariant always holds
//      test_index_in_range.dfy(9,19)-(9,24): loop invariant always holds
//      test_index_in_range.dfy(13,9)-(13,19): assignment (or return)

// Need to investigate more why that is the case for now I can just signalat it

// Showing that the assertion the same is counted two times ! making the size of the minimum
// unsat core wrongly 3. Possibly this is masking the case on the top. As by having
// This wrongly being 3 it gets the same size as the other that is also 3.

//::: Name - Repeated assertion in proofCore Extraction
//::: To see this tested why was found you must see L5 and uncomment that line (it appears on the core of assertion on line 9)
//::: I think it is because of the bug
//::: L5 - Uncovered