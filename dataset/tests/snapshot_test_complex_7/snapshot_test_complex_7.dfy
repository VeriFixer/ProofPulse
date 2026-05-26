// Forall
method Q1(){
    var a := new int[6];
    a[0], a[1], a[2], a[3], a[4], a[5] := 1,0,0,0,1,1;
    var b := new int[3];
    b[0], b[1], b[2] := 1, 0, 1;

    var j,k := 1,3;
    var p,r := 4,5;


    // a) All elements in the range a[j..k] == 0
    assert(forall i : int :: j<= i <= k ==> a[i] == 0);
    assert(forall i : int :: if j <= i <= k then a[i] == 0 else true);

    // b) All zeros in a occur in the interval a[j..k]
    assert(forall i : int :: (0 <= i < a.Length && a[i] == 0) ==> j <= i <= k);

    // c) It is *not* the case that all ones of a occur in the interval in a[p..r]

    assert(a[0] == 1); // helps the next assertion verify

    assert(!(forall i : int :: (0 <= i < a.Length && a[i] == 1) ==> p <= i <= r));

    // d) a[0..n-1] contains at least two zeros

    assert(a[1] == 0 && a[2] == 0);
    assert(exists i, j : int :: 0 <= i < j < a.Length && a[i] == 0 && a[j] == 0);

    // e) b[0..n-1] contains at the most two zeros (Note: *not* true for array a)
    assert(!(exists i, j, k : int :: 0 <= i < j< k < b.Length && b[i] == 0 && b[j] == 0 && b[k] == k));
}

// Quantifiers
class Secret{
    var secret : int;
    var known : bool;
    var count : int;

    method Init(x : int)
    modifies `secret, `known, `count
    requires 1 <= x <= 10
    ensures secret == x
    ensures known == false
    ensures count == 0
    {
        known := false;
        count := 0;
        secret := x;
    }

    method Guess(g : int) returns (result : bool, guesses : int)
    modifies `known, `count
    requires known == false
    ensures if g == secret then 
                result == true && known == true 
            else 
                result == false && known == false
    ensures count == old(count) + 1 && guesses == count
    {
        if (g == secret)
        {
            known := true;
            result := true;
        }
        else
        {
            result := false;
        }
        count := count + 1;
        guesses := count;
    }

    method Main()
    {
        var testObject : Secret := new Secret.Init(5);
        assert(1 <= testObject.secret <= 10);
        assert(testObject.secret == 5);
        var x, y := testObject.Guess(0);

        assert(x == false && y == 1);

        x,y := testObject.Guess(5);

        assert(x == true && y == 2);

        //x,y := testObject.Guess(5);

    }
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 3
//::       col: 22
//::     end:
//::       line: 3
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 3
//::       col: 22
//::     end:
//::       line: 3
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 3
//::       col: 9
//::     end:
//::       line: 3
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 11
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 17
//::     end:
//::       line: 4
//::       col: 17
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 17
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 23
//::     end:
//::       line: 4
//::       col: 23
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 23
//::     end:
//::       line: 4
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 29
//::     end:
//::       line: 4
//::       col: 29
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 29
//::     end:
//::       line: 4
//::       col: 32
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 35
//::     end:
//::       line: 4
//::       col: 35
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 35
//::     end:
//::       line: 4
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 54
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 14
//::     prooftext: left-hand sides a[1] and a[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 17
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: left-hand sides a[2] and a[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 23
//::     end:
//::       line: 4
//::       col: 26
//::     prooftext: left-hand sides a[3] and a[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 29
//::     end:
//::       line: 4
//::       col: 32
//::     prooftext: left-hand sides a[4] and a[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 35
//::     end:
//::       line: 4
//::       col: 38
//::     prooftext: left-hand sides a[5] and a[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 5
//::       col: 22
//::     end:
//::       line: 5
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 11
//::     end:
//::       line: 6
//::       col: 11
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 11
//::     end:
//::       line: 6
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 17
//::     end:
//::       line: 6
//::       col: 17
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 17
//::     end:
//::       line: 6
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 32
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 11
//::     end:
//::       line: 6
//::       col: 14
//::     prooftext: left-hand sides b[1] and b[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 17
//::     end:
//::       line: 6
//::       col: 20
//::     prooftext: left-hand sides b[2] and b[0] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 9
//::       col: 9
//::     end:
//::       line: 9
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 13
//::       col: 45
//::     end:
//::       line: 13
//::       col: 45
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 13
//::       col: 45
//::     end:
//::       line: 13
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 13
//::       col: 5
//::     end:
//::       line: 13
//::       col: 55
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 14
//::       col: 50
//::     end:
//::       line: 14
//::       col: 50
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 14
//::       col: 50
//::     end:
//::       line: 14
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
//::       col: 70
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 40
//::     end:
//::       line: 17
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 52
//::     end:
//::       line: 17
//::       col: 52
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 52
//::     end:
//::       line: 17
//::       col: 55
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 5
//::     end:
//::       line: 17
//::       col: 79
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 21
//::       col: 12
//::     end:
//::       line: 21
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 21
//::       col: 12
//::     end:
//::       line: 21
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 21
//::       col: 5
//::     end:
//::       line: 21
//::       col: 22
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 42
//::     end:
//::       line: 23
//::       col: 44
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 54
//::     end:
//::       line: 23
//::       col: 54
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 54
//::     end:
//::       line: 23
//::       col: 57
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 82
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 12
//::     end:
//::       line: 27
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 12
//::     end:
//::       line: 27
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 25
//::     end:
//::       line: 27
//::       col: 25
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 25
//::     end:
//::       line: 27
//::       col: 28
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 12
//::     end:
//::       line: 27
//::       col: 20
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 25
//::     end:
//::       line: 27
//::       col: 33
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 11
//::     end:
//::       line: 27
//::       col: 34
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 46
//::     end:
//::       line: 28
//::       col: 48
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 58
//::     end:
//::       line: 28
//::       col: 58
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 58
//::     end:
//::       line: 28
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 71
//::     end:
//::       line: 28
//::       col: 71
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 71
//::     end:
//::       line: 28
//::       col: 74
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 5
//::     end:
//::       line: 28
//::       col: 81
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 54
//::     end:
//::       line: 31
//::       col: 56
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 66
//::     end:
//::       line: 31
//::       col: 66
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 66
//::     end:
//::       line: 31
//::       col: 69
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 79
//::     end:
//::       line: 31
//::       col: 79
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 79
//::     end:
//::       line: 31
//::       col: 82
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 92
//::     end:
//::       line: 31
//::       col: 92
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 92
//::     end:
//::       line: 31
//::       col: 95
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 5
//::     end:
//::       line: 31
//::       col: 103
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,6-4,6|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 6
//::     end:
//::       line: 4
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,12-4,12|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,18-4,18|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 18
//::     end:
//::       line: 4
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,24-4,24|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 24
//::     end:
//::       line: 4
//::       col: 24
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,30-4,30|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 30
//::     end:
//::       line: 4
//::       col: 30
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|4,36-4,36|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 4
//::       col: 36
//::     end:
//::       line: 4
//::       col: 36
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 5
//::       col: 22
//::     end:
//::       line: 5
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,6-6,6|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 6
//::     end:
//::       line: 6
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,12-6,12|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 12
//::     end:
//::       line: 6
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|6,18-6,18|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 6
//::       col: 18
//::     end:
//::       line: 6
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 13
//::       col: 5
//::     end:
//::       line: 13
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 5
//::     end:
//::       line: 17
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|21,13-21,13|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 21
//::       col: 13
//::     end:
//::       line: 21
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 21
//::       col: 5
//::     end:
//::       line: 21
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,13-27,13|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 13
//::     end:
//::       line: 27
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,17-27,17|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 17
//::     end:
//::       line: 27
//::       col: 17
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,30-27,30|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 30
//::     end:
//::       line: 27
//::       col: 30
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 5
//::     end:
//::       line: 28
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,5|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 5
//::     end:
//::       line: 31
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,93-31,93|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 93
//::     end:
//::       line: 31
//::       col: 93
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,80-31,80|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 80
//::     end:
//::       line: 31
//::       col: 80
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,67-31,67|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 67
//::     end:
//::       line: 31
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|31,56-31,56|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 31
//::       col: 56
//::     end:
//::       line: 31
//::       col: 56
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,72-28,72|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 72
//::     end:
//::       line: 28
//::       col: 72
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,59-28,59|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 59
//::     end:
//::       line: 28
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|28,48-28,48|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 28
//::       col: 48
//::     end:
//::       line: 28
//::       col: 48
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|27,26-27,26|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 27
//::       col: 26
//::     end:
//::       line: 27
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,55-23,55|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 55
//::     end:
//::       line: 23
//::       col: 55
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|23,44-23,44|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 23
//::       col: 44
//::     end:
//::       line: 23
//::       col: 44
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,53-17,53|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 53
//::     end:
//::       line: 17
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|17,42-17,42|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 17
//::       col: 42
//::     end:
//::       line: 17
//::       col: 42
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|14,51-14,51|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 14
//::       col: 51
//::     end:
//::       line: 14
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: snapshot_test_complex_7.dfy|Q1|correctness|13,46-13,46|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 13
//::       col: 46
//::     end:
//::       line: 13
//::       col: 46
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Q1
//::     methodType: correctness
//::     assertionGroup: Q1
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 15
//::     end:
//::       line: 41
//::       col: 15
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 15
//::     end:
//::       line: 41
//::       col: 15
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|42,14-42,24|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 42
//::       col: 14
//::     end:
//::       line: 42
//::       col: 24
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 24
//::     end:
//::       line: 41
//::       col: 24
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 32
//::     end:
//::       line: 41
//::       col: 32
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|43,13-43,23|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 43
//::       col: 13
//::     end:
//::       line: 43
//::       col: 23
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|44,13-44,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 44
//::       col: 13
//::     end:
//::       line: 44
//::       col: 22
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|45,13-45,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 45
//::       col: 13
//::     end:
//::       line: 45
//::       col: 22
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 24
//::     end:
//::       line: 41
//::       col: 24
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 41
//::       col: 32
//::     end:
//::       line: 41
//::       col: 32
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: well-formedness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 47
//::       col: 9
//::     end:
//::       line: 47
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 47
//::       col: 9
//::     end:
//::       line: 47
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 42
//::       col: 14
//::     end:
//::       line: 42
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 42
//::       col: 19
//::     end:
//::       line: 42
//::       col: 24
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 43
//::       col: 13
//::     end:
//::       line: 43
//::       col: 23
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 44
//::       col: 13
//::     end:
//::       line: 44
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 45
//::       col: 13
//::     end:
//::       line: 45
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 47
//::       col: 9
//::     end:
//::       line: 47
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 48
//::       col: 9
//::     end:
//::       line: 48
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 48
//::       col: 9
//::     end:
//::       line: 48
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 49
//::       col: 9
//::     end:
//::       line: 49
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 49
//::       col: 9
//::     end:
//::       line: 49
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 48
//::       col: 9
//::     end:
//::       line: 48
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 49
//::       col: 9
//::     end:
//::       line: 49
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|43,20-43,20|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 43
//::       col: 20
//::     end:
//::       line: 43
//::       col: 20
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|44,19-44,19|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 44
//::       col: 19
//::     end:
//::       line: 44
//::       col: 19
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Init|correctness|45,19-45,19|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 45
//::       col: 19
//::     end:
//::       line: 45
//::       col: 19
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Init
//::     methodType: correctness
//::     assertionGroup: Secret.Init
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 53
//::       col: 15
//::     end:
//::       line: 53
//::       col: 15
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 53
//::       col: 15
//::     end:
//::       line: 53
//::       col: 15
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|54,14-54,23|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 54
//::       col: 14
//::     end:
//::       line: 54
//::       col: 23
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 53
//::       col: 23
//::     end:
//::       line: 53
//::       col: 23
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|55,16-55,21|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 55
//::       col: 16
//::     end:
//::       line: 55
//::       col: 21
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,17-56,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 17
//::     end:
//::       line: 56
//::       col: 27
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,35-56,44|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 35
//::     end:
//::       line: 56
//::       col: 44
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,17-58,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 17
//::     end:
//::       line: 58
//::       col: 27
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,36-58,45|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 36
//::     end:
//::       line: 58
//::       col: 45
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 26
//::     end:
//::       line: 59
//::       col: 26
//::     prooftext: receiver is always allocated in the state in which its fields are accessed
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,13-59,35|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 13
//::     end:
//::       line: 59
//::       col: 35
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,40-59,51|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 40
//::     end:
//::       line: 59
//::       col: 51
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 53
//::       col: 23
//::     end:
//::       line: 53
//::       col: 23
//::     prooftext: frame expression does not dereference null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 26
//::     end:
//::       line: 59
//::       col: 26
//::     prooftext: receiver is always allocated in the state in which its fields are accessed
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: well-formedness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 70
//::       col: 9
//::     end:
//::       line: 70
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 70
//::       col: 9
//::     end:
//::       line: 70
//::       col: 9
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 54
//::       col: 14
//::     end:
//::       line: 54
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 17
//::     end:
//::       line: 56
//::       col: 27
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 35
//::     end:
//::       line: 56
//::       col: 44
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 17
//::     end:
//::       line: 58
//::       col: 27
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 36
//::     end:
//::       line: 58
//::       col: 45
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 13
//::     end:
//::       line: 59
//::       col: 35
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 40
//::     end:
//::       line: 59
//::       col: 51
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 13
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 26
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 64
//::       col: 13
//::     end:
//::       line: 64
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 68
//::       col: 13
//::     end:
//::       line: 68
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 70
//::       col: 9
//::     end:
//::       line: 70
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 71
//::       col: 9
//::     end:
//::       line: 71
//::       col: 25
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 72
//::       col: 5
//::     end:
//::       line: 72
//::       col: 5
//::     prooftext: >-
//::       out-parameter 'result', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,24-56,24|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 24
//::     end:
//::       line: 56
//::       col: 24
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,41-56,41|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 41
//::     end:
//::       line: 56
//::       col: 41
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,24-58,24|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 24
//::     end:
//::       line: 58
//::       col: 24
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,42-58,42|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 42
//::     end:
//::       line: 58
//::       col: 42
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,19-59,19|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 19
//::     end:
//::       line: 59
//::       col: 19
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,48-59,48|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 48
//::     end:
//::       line: 59
//::       col: 48
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 63
//::       col: 13
//::     end:
//::       line: 63
//::       col: 13
//::     prooftext: an object is in the enclosing context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Guess
//::     methodType: correctness
//::     assertionGroup: Secret.Guess
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|76,47-76,47|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 76
//::       col: 47
//::     end:
//::       line: 76
//::       col: 47
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 76
//::       col: 13
//::     end:
//::       line: 76
//::       col: 54
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 21
//::     end:
//::       line: 77
//::       col: 21
//::     prooftext: >-
//::       variable 'testObject', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 21
//::     end:
//::       line: 77
//::       col: 32
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 16
//::     end:
//::       line: 77
//::       col: 32
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 21
//::     end:
//::       line: 77
//::       col: 42
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 15
//::     end:
//::       line: 77
//::       col: 44
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 78
//::       col: 16
//::     end:
//::       line: 78
//::       col: 16
//::     prooftext: >-
//::       variable 'testObject', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 78
//::       col: 16
//::     end:
//::       line: 78
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 78
//::       col: 9
//::     end:
//::       line: 78
//::       col: 39
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 79
//::       col: 21
//::     end:
//::       line: 79
//::       col: 21
//::     prooftext: >-
//::       variable 'testObject', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 79
//::       col: 13
//::     end:
//::       line: 79
//::       col: 40
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 81
//::       col: 16
//::     end:
//::       line: 81
//::       col: 21
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 81
//::       col: 30
//::     end:
//::       line: 81
//::       col: 35
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 81
//::       col: 15
//::     end:
//::       line: 81
//::       col: 36
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 83
//::       col: 16
//::     end:
//::       line: 83
//::       col: 16
//::     prooftext: >-
//::       variable 'testObject', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 83
//::       col: 9
//::     end:
//::       line: 83
//::       col: 35
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 85
//::       col: 16
//::     end:
//::       line: 85
//::       col: 21
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 85
//::       col: 29
//::     end:
//::       line: 85
//::       col: 34
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 85
//::       col: 15
//::     end:
//::       line: 85
//::       col: 35
//::     prooftext: assert statement
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|76,47-76,47|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 76
//::       col: 47
//::     end:
//::       line: 76
//::       col: 47
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 76
//::       col: 13
//::     end:
//::       line: 76
//::       col: 54
//::     prooftext: requires clause at snapshot_test_complex_7.dfy(42,14)-(42,19) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|42,14-42,19|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 42
//::       col: 14
//::     end:
//::       line: 42
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|42,19-42,24|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 42
//::       col: 19
//::     end:
//::       line: 42
//::       col: 24
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,32-77,32|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 32
//::     end:
//::       line: 77
//::       col: 32
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,18-77,18|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 18
//::     end:
//::       line: 77
//::       col: 18
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|43,13-43,23|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 43
//::       col: 13
//::     end:
//::       line: 43
//::       col: 23
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|77,39-77,39|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 77
//::       col: 39
//::     end:
//::       line: 77
//::       col: 39
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|78,27-78,27|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 78
//::       col: 27
//::     end:
//::       line: 78
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,9|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 78
//::       col: 9
//::     end:
//::       line: 78
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|79,37-79,37|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 79
//::       col: 37
//::     end:
//::       line: 79
//::       col: 37
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|79,37-79,37|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 79
//::       col: 37
//::     end:
//::       line: 79
//::       col: 37
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|44,13-44,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 44
//::       col: 13
//::     end:
//::       line: 44
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 79
//::       col: 13
//::     end:
//::       line: 79
//::       col: 40
//::     prooftext: requires clause at snapshot_test_complex_7.dfy(54,14)-(54,23) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|54,14-54,23|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 54
//::       col: 14
//::     end:
//::       line: 54
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|81,18-81,18|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 81
//::       col: 18
//::     end:
//::       line: 81
//::       col: 18
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|58,17-58,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 17
//::     end:
//::       line: 58
//::       col: 27
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|81,32-81,32|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 81
//::       col: 32
//::     end:
//::       line: 81
//::       col: 32
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|45,13-45,22|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 45
//::       col: 13
//::     end:
//::       line: 45
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|59,13-59,35|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 13
//::     end:
//::       line: 59
//::       col: 35
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|59,40-59,51|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 59
//::       col: 40
//::     end:
//::       line: 59
//::       col: 51
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|83,32-83,32|AssertionAutomatic
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 83
//::       col: 32
//::     end:
//::       line: 83
//::       col: 32
//::     prooftext: call is allowed by context's modifies clause
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|83,32-83,32|Precondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 83
//::       col: 32
//::     end:
//::       line: 83
//::       col: 32
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|56,17-56,27|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 56
//::       col: 17
//::     end:
//::       line: 56
//::       col: 27
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|58,36-58,45|Postcondition
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 58
//::       col: 36
//::     end:
//::       line: 58
//::       col: 45
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|Call
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 83
//::       col: 9
//::     end:
//::       line: 83
//::       col: 35
//::     prooftext: requires clause at snapshot_test_complex_7.dfy(54,14)-(54,23) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|85,18-85,18|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 85
//::       col: 18
//::     end:
//::       line: 85
//::       col: 18
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//::   - id: >-
//::       snapshot_test_complex_7.dfy|Secret.Main|correctness|85,31-85,31|AssertionManual
//::     file: snapshot_test_complex_7.dfy
//::     start:
//::       line: 85
//::       col: 31
//::     end:
//::       line: 85
//::       col: 31
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Secret.Main
//::     methodType: correctness
//::     assertionGroup: Secret.Main
//:: edges:
//::   tops:
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,6-4,6|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,12-4,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,18-4,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,24-4,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,30-4,30|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|4,36-4,36|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|6,6-6,6|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|6,12-6,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|6,18-6,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|21,13-21,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|27,13-27,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|27,17-27,17|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|27,30-27,30|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|31,93-31,93|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|31,80-31,80|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|31,67-31,67|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|31,56-31,56|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|28,72-28,72|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|28,59-28,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|28,48-28,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|27,26-27,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|23,55-23,55|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|23,44-23,44|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|17,53-17,53|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|17,42-17,42|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|14,51-14,51|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Q1|correctness|13,46-13,46|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,48|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,22-3,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|3,9-3,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,5-4,54|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,11-4,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,17-4,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,23-4,26|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,29-4,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|4,35-4,38|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,22-5,22|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|5,9-5,24|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,5|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,5-6,32|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,11-6,14|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|6,17-6,20|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|8,9-8,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Q1|correctness|9,9-9,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|13,45-13,45|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|13,5-13,55|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|14,50-14,53|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|14,5-14,70|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,40-17,42|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|17,52-17,55|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|17,5-17,79|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|21,12-21,15|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|21,5-21,22|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,42-23,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|23,54-23,57|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|23,5-23,82|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,28|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,12-27,20|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,25-27,33|AssertionManual
//::         - snapshot_test_complex_7.dfy|Q1|correctness|27,11-27,34|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,46-28,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,58|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,58-28,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,71|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|28,71-28,74|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|28,5-28,81|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,54-31,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,66|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,66-31,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,79|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,79-31,82|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,92|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Q1|correctness|31,92-31,95|AssertionAutomatic
//::         - snapshot_test_complex_7.dfy|Q1|correctness|31,5-31,103|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|42,14-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|45,13-45,22|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|42,14-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|45,13-45,22|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,32-41,32|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|42,14-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,15-41,15|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|41,24-41,24|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|well-formedness|45,13-45,22|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|43,20-43,20|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|44,19-44,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Init|correctness|45,19-45,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|45,13-45,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,19|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|44,13-44,22|Postcondition
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|47,9-47,23|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|48,9-48,9|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Init|correctness|49,9-49,20|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|55,16-55,21|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,40-59,51|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|55,16-55,21|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,40-59,51|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,26-59,26|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,15-53,15|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|53,23-53,23|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|55,16-55,21|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|well-formedness|59,40-59,51|Postcondition
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,24-56,24|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,41-56,41|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,24-58,24|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,42-58,42|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,19-59,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,48-59,48|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|56,35-56,44|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|58,36-58,45|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|63,13-63,26|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|64,13-64,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|68,13-68,28|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,9|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|70,9-70,27|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|71,9-71,25|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Guess|correctness|72,5-72,5|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|76,47-76,47|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|76,47-76,47|Precondition
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|77,32-77,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|77,18-77,18|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|77,39-77,39|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|78,27-78,27|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,9|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|79,37-79,37|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|79,37-79,37|Precondition
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|81,18-81,18|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|81,32-81,32|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|83,32-83,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|83,32-83,32|Precondition
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|85,18-85,18|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::     - id: >-
//::         snapshot_test_complex_7.dfy|Secret.Main|correctness|85,31-85,31|AssertionManual
//::       provedBy:
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::         - snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|Call
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,29-85,34|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,16-77,32|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,21-77,42|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|77,15-77,44|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,16-78,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|78,9-78,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,21-79,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,16-81,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,30-81,35|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|81,15-81,36|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,16-83,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|CodeLine
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,16-85,21|AssertionManual
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|85,15-85,35|CodeLine
//::   calls:
//::     - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|76,13-76,54|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|42,14-42,19|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|42,19-42,24|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|43,13-43,23|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|44,13-44,22|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|45,13-45,22|Postcondition
//::     - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|79,13-79,40|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|58,17-58,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|59,40-59,51|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|58,36-58,45|Postcondition
//::     - id: snapshot_test_complex_7.dfy|Secret.Main|correctness|83,9-83,35|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|54,14-54,23|Precondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|56,17-56,27|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|59,13-59,35|Postcondition
//::         - >-
//::           snapshot_test_complex_7.dfy|Secret.Main|correctness|59,40-59,51|Postcondition
//::
