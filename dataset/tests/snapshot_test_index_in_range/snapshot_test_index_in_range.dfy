method zeroVector(n : array<int>) returns (ex:array<int>)
    ensures n.Length == ex.Length
    ensures forall i:int :: 0<= i < n.Length ==> ex[i] == 0
{
    var z:= 0;
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
//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|6,21-6,21|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 21
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 14
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 29
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 24
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 49
//::     end:
//::       line: 10
//::       col: 49
//::     prooftext: >-
//::       variable 'ex', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 49
//::     end:
//::       line: 10
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 58
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 9
//::     prooftext: >-
//::       variable 'ex', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 14
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 15
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'ex', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,21-9,21|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 21
//::     end:
//::       line: 9
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,26-9,26|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
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
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,19|LoopInvariant
//::     file: snapshot_test_index_in_range.dfy
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
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|8,17-8,17|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 17
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|12,11-12,11|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 11
//::     end:
//::       line: 12
//::       col: 11
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-8,5|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|2,22-2,22|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 22
//::     end:
//::       line: 2
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,13|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|10,51-10,51|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 51
//::     end:
//::       line: 10
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|correctness|9,31-9,31|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 31
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,15-2,15|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 15
//::     end:
//::       line: 2
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 25
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 37
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 50
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 54
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,28-2,28|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 28
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,52-3,52|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 52
//::     end:
//::       line: 3
//::       col: 52
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,39-3,39|AssertionAutomatic
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 39
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|6,21-6,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|9,21-9,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|9,26-9,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|8,17-8,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|12,11-12,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-8,5|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|2,22-2,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|10,51-10,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|correctness|9,31-9,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58|LoopInvariant
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5|CodeLine
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,15-2,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,28-2,28|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,52-3,52|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,39-3,39|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_test_index_in_range.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::   calls: []
//::
