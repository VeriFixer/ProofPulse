method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
    var minVal := a[0];
    var maxVal := a[0];
    for i := 1 to a.Length
        invariant 1 <= i <= a.Length
        invariant minVal <= maxVal
        invariant forall k :: 0 <= k < i ==> minVal <= a[k] && a[k] <= maxVal
        invariant minVal == Min(a[..i])
        invariant maxVal == Max(a[..i])
    {
        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
        assert a[..i+1][..i] == a[..i];
    }
    assert a[..a.Length] == a[..];
    diff := maxVal - minVal;
}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var minPrefix := Min(a[..|a|-1]);
      if a[|a|-1] <= minPrefix then a[|a|-1] else minPrefix
}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
      var maxPrefix := Max(a[..|a|-1]);
      if a[|a|-1] >= maxPrefix then a[|a|-1] else maxPrefix
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,16-2,16|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 2
//::       col: 16
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,16|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,25|Precondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 25
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,26-3,26|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 26
//::     end:
//::       line: 3
//::       col: 26
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,22-3,31|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 22
//::     end:
//::       line: 3
//::       col: 31
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,39-3,39|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 39
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,35-3,44|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 35
//::     end:
//::       line: 3
//::       col: 44
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,13-3,45|Postcondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 45
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,25-3,25|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,38-3,38|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 38
//::     end:
//::       line: 3
//::       col: 38
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: well-formedness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 5
//::       col: 19
//::     end:
//::       line: 5
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 25
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 45
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 5
//::       col: 19
//::     end:
//::       line: 5
//::       col: 22
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 22
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 29
//::     end:
//::       line: 8
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 24
//::     end:
//::       line: 8
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 29
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 56
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 64
//::     end:
//::       line: 10
//::       col: 64
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 64
//::     end:
//::       line: 10
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 72
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 33
//::     end:
//::       line: 11
//::       col: 33
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 33
//::     end:
//::       line: 11
//::       col: 38
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 29
//::     end:
//::       line: 11
//::       col: 39
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 39
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 33
//::     end:
//::       line: 12
//::       col: 33
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 33
//::     end:
//::       line: 12
//::       col: 38
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 29
//::     end:
//::       line: 12
//::       col: 39
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 19
//::     end:
//::       line: 12
//::       col: 39
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 14
//::       col: 12
//::     end:
//::       line: 14
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 14
//::       col: 12
//::     end:
//::       line: 14
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 15
//::       col: 23
//::     end:
//::       line: 15
//::       col: 23
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 15
//::       col: 23
//::     end:
//::       line: 15
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 15
//::       col: 13
//::     end:
//::       line: 15
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 16
//::       col: 19
//::     end:
//::       line: 16
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 16
//::       col: 19
//::     end:
//::       line: 16
//::       col: 22
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 17
//::       col: 23
//::     end:
//::       line: 17
//::       col: 23
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 17
//::       col: 23
//::     end:
//::       line: 17
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 17
//::       col: 13
//::     end:
//::       line: 17
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 16
//::     end:
//::       line: 19
//::       col: 16
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 16
//::     end:
//::       line: 19
//::       col: 23
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 16
//::     end:
//::       line: 19
//::       col: 28
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 33
//::     end:
//::       line: 19
//::       col: 33
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 33
//::     end:
//::       line: 19
//::       col: 38
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 39
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
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
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 16
//::     end:
//::       line: 21
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 12
//::     end:
//::       line: 21
//::       col: 24
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 29
//::     end:
//::       line: 21
//::       col: 29
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 5
//::     end:
//::       line: 21
//::       col: 34
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 22
//::       col: 5
//::     end:
//::       line: 22
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 23
//::       col: 1
//::     end:
//::       line: 23
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'diff', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,20-5,20|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 5
//::       col: 20
//::     end:
//::       line: 5
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,20-6,20|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 6
//::       col: 20
//::     end:
//::       line: 6
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,21-7,21|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 7
//::       col: 21
//::     end:
//::       line: 7
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,21-8,21|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 21
//::     end:
//::       line: 8
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,26-8,26|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 26
//::     end:
//::       line: 8
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,26-9,26|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 9
//::       col: 26
//::     end:
//::       line: 9
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,19|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,26-11,26|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 26
//::     end:
//::       line: 11
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|25,1-32,1|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 25
//::       col: 1
//::     end:
//::       line: 32
//::       col: 1
//::     prooftext: function definition for Min
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,26-12,26|LoopInvariant
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 26
//::     end:
//::       line: 12
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|34,1-41,1|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 34
//::       col: 1
//::     end:
//::       line: 41
//::       col: 1
//::     prooftext: function definition for Max
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,13-14,13|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 14
//::       col: 13
//::     end:
//::       line: 14
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,20-16,20|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 16
//::       col: 20
//::     end:
//::       line: 16
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,17-19,17|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 17
//::     end:
//::       line: 19
//::       col: 17
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,24-19,24|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 24
//::     end:
//::       line: 19
//::       col: 24
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,34-19,34|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 34
//::     end:
//::       line: 19
//::       col: 34
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,9|AssertionManual
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 9
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,24-17,24|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 17
//::       col: 24
//::     end:
//::       line: 17
//::       col: 24
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,24-15,24|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 15
//::       col: 24
//::     end:
//::       line: 15
//::       col: 24
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,18-21,18|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 18
//::     end:
//::       line: 21
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,13-21,13|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 21
//::       col: 13
//::     end:
//::       line: 21
//::       col: 13
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,5|AssertionManual
//::     file: snapshot_test_complex_11.dfy
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
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,18-3,18|Postcondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 3
//::       col: 18
//::     end:
//::       line: 3
//::       col: 18
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,34-11,34|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 34
//::     end:
//::       line: 11
//::       col: 34
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,32-11,32|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 11
//::       col: 32
//::     end:
//::       line: 11
//::       col: 32
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,34-12,34|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 34
//::     end:
//::       line: 12
//::       col: 34
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,32-12,32|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 12
//::       col: 32
//::     end:
//::       line: 12
//::       col: 32
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,57-10,57|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 57
//::     end:
//::       line: 10
//::       col: 57
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,65-10,65|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 10
//::       col: 65
//::     end:
//::       line: 10
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,31-8,31|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 8
//::       col: 31
//::     end:
//::       line: 8
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DifferenceMinMax
//::     methodType: correctness
//::     assertionGroup: DifferenceMinMax
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|28,23-28,23|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 28
//::       col: 23
//::     end:
//::       line: 28
//::       col: 23
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 28
//::       col: 22
//::     end:
//::       line: 28
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 26
//::       col: 14
//::     end:
//::       line: 26
//::       col: 20
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 28
//::       col: 22
//::     end:
//::       line: 28
//::       col: 25
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 25
//::       col: 1
//::     end:
//::       line: 32
//::       col: 1
//::     prooftext: function definition for Min
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 30
//::       col: 28
//::     end:
//::       line: 30
//::       col: 37
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 30
//::       col: 24
//::     end:
//::       line: 30
//::       col: 38
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 30
//::       col: 11
//::     end:
//::       line: 30
//::       col: 11
//::     prooftext: let expression binding
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 10
//::     end:
//::       line: 31
//::       col: 17
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 37
//::     end:
//::       line: 31
//::       col: 44
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 37
//::     end:
//::       line: 31
//::       col: 44
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 51
//::     end:
//::       line: 31
//::       col: 51
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|30,29-30,29|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 30
//::       col: 29
//::     end:
//::       line: 30
//::       col: 29
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|30,27-30,27|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 30
//::       col: 27
//::     end:
//::       line: 30
//::       col: 27
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|31,11-31,11|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 11
//::     end:
//::       line: 31
//::       col: 11
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Min|well-formedness|31,38-31,38|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 31
//::       col: 38
//::     end:
//::       line: 31
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Min
//::     methodType: well-formedness
//::     assertionGroup: Min
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|37,23-37,23|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 37
//::       col: 23
//::     end:
//::       line: 37
//::       col: 23
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 37
//::       col: 22
//::     end:
//::       line: 37
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 35
//::       col: 14
//::     end:
//::       line: 35
//::       col: 20
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 37
//::       col: 22
//::     end:
//::       line: 37
//::       col: 25
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 34
//::       col: 1
//::     end:
//::       line: 41
//::       col: 1
//::     prooftext: function definition for Max
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 39
//::       col: 28
//::     end:
//::       line: 39
//::       col: 37
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 39
//::       col: 24
//::     end:
//::       line: 39
//::       col: 38
//::     prooftext: function precondition satisfied
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 39
//::       col: 11
//::     end:
//::       line: 39
//::       col: 11
//::     prooftext: let expression binding
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 10
//::     end:
//::       line: 40
//::       col: 17
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 37
//::     end:
//::       line: 40
//::       col: 44
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 37
//::     end:
//::       line: 40
//::       col: 44
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 51
//::     end:
//::       line: 40
//::       col: 51
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|39,29-39,29|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 39
//::       col: 29
//::     end:
//::       line: 39
//::       col: 29
//::     prooftext: upper bound within range of sequence
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|39,27-39,27|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 39
//::       col: 27
//::     end:
//::       line: 39
//::       col: 27
//::     prooftext: function precondition satisfied
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|40,11-40,11|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 11
//::     end:
//::       line: 40
//::       col: 11
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_test_complex_11.dfy|Max|well-formedness|40,38-40,38|AssertionAutomatic
//::     file: snapshot_test_complex_11.dfy
//::     start:
//::       line: 40
//::       col: 38
//::     end:
//::       line: 40
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: well-formedness
//::     assertionGroup: Max
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,16-2,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,26-3,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,22-3,31|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,39-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,35-3,44|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,13-3,45|Postcondition
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,25-3,25|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,22-3,31|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,26-3,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,39-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,35-3,44|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,13-3,45|Postcondition
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,38-3,38|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,35-3,44|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,26-3,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,22-3,31|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,39-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|well-formedness|3,13-3,45|Postcondition
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,20-5,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,20-6,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,21-7,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,21-8,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,26-8,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,26-9,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,26-11,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|25,1-32,1|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,26-12,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|25,1-32,1|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|34,1-41,1|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,13-14,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,20-16,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,17-19,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,24-19,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,34-19,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,9|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,24-17,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,24-15,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,18-21,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,13-21,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,18-3,18|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,34-11,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,32-11,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,34-12,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,32-12,32|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,57-10,57|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,65-10,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,31-8,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,29-8,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|2,14-2,25|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|3,13-3,45|Postcondition
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,19-5,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|5,9-5,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,19-6,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|6,9-6,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,19-8,24|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|8,24-8,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|9,19-9,29|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,64-10,67|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|10,19-10,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,33-11,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,29-11,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|11,19-11,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,33-12,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,29-12,39|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|12,19-12,39|LoopInvariant
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|14,12-14,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,23-15,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|15,13-15,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|16,19-16,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,23|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,23-17,26|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|17,13-17,27|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,23|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,16-19,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,33|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,33-19,38|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|19,9-19,39|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,16-21,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,12-21,24|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,29-21,29|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|21,5-21,34|AssertionManual
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|22,5-22,28|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|DifferenceMinMax|correctness|23,1-23,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Min|well-formedness|28,23-28,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Min|well-formedness|30,29-30,29|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Min|well-formedness|30,27-30,27|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Min|well-formedness|31,11-31,11|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Min|well-formedness|31,38-31,38|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,28-30,37|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|26,14-26,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|28,22-28,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|25,1-32,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,24-30,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|30,11-30,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Min|well-formedness|31,10-31,17|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,37-31,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Min|well-formedness|31,51-31,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Max|well-formedness|37,23-37,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Max|well-formedness|39,29-39,29|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Max|well-formedness|39,27-39,27|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Max|well-formedness|40,11-40,11|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::     - id: >-
//::         snapshot_test_complex_11.dfy|Max|well-formedness|40,38-40,38|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,28-39,37|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|35,14-35,20|Precondition
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|37,22-37,25|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|34,1-41,1|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,24-39,38|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|39,11-39,11|CodeLine
//::         - >-
//::           snapshot_test_complex_11.dfy|Max|well-formedness|40,10-40,17|AssertionAutomatic
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,37-40,44|CodeLine
//::         - snapshot_test_complex_11.dfy|Max|well-formedness|40,51-40,51|CodeLine
//::   calls: []
//::
