predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
    result := true;
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant result <==> forall k :: 0 <= k < i ==> (IsEven(k) ==> IsEven(lst[k]))
    {
        if IsEven(i) && !IsEven(lst[i])
        {
            result := false;
            break;
        }
    }
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,7-3,7|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 3
//::       col: 7
//::     end:
//::       line: 3
//::       col: 7
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEven
//::     methodType: well-formedness
//::     assertionGroup: IsEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,9|CodeLine
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 9
//::     prooftext: divisor is always non-zero.
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEven
//::     methodType: well-formedness
//::     assertionGroup: IsEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,14|CodeLine
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 14
//::     prooftext: function call result
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsEven
//::     methodType: well-formedness
//::     assertionGroup: IsEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 10
//::       col: 14
//::     end:
//::       line: 10
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 10
//::       col: 14
//::     end:
//::       line: 10
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 13
//::     end:
//::       line: 7
//::       col: 85
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 33
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 24
//::     end:
//::       line: 11
//::       col: 33
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 19
//::     end:
//::       line: 12
//::       col: 19
//::     prooftext: >-
//::       variable 'result', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 80
//::     end:
//::       line: 12
//::       col: 85
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 19
//::     end:
//::       line: 12
//::       col: 87
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 14
//::       col: 33
//::     end:
//::       line: 14
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 16
//::       col: 13
//::     end:
//::       line: 16
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 20
//::       col: 1
//::     end:
//::       line: 20
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'result', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,21-11,21|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 21
//::     end:
//::       line: 11
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,26-11,26|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
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
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,26-12,26|LoopInvariant
//::     file: snapshot_bug_predicate_body_uncovered.dfy
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
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,20-7,20|Postcondition
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 20
//::     end:
//::       line: 7
//::       col: 20
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,36-14,36|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 14
//::       col: 36
//::     end:
//::       line: 14
//::       col: 36
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,83-12,83|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 83
//::     end:
//::       line: 12
//::       col: 83
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,81-7,81|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 81
//::     end:
//::       line: 7
//::       col: 81
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: well-formedness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,78-7,83|AssertionAutomatic
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 78
//::     end:
//::       line: 7
//::       col: 83
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: IsEvenAtIndexEven
//::     methodType: well-formedness
//::     assertionGroup: IsEvenAtIndexEven
//::   - id: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,13-7,85|Postcondition
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 13
//::     end:
//::       line: 7
//::       col: 85
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: IsEvenAtIndexEven
//::     methodType: well-formedness
//::     assertionGroup: IsEvenAtIndexEven
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,7-3,7|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,9|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,14|CodeLine
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,21-11,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,26-11,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,26-12,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,20-7,20|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,36-14,36|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,83-12,83|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85|Postcondition
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87|LoopInvariant
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28|CodeLine
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,81-7,81|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,78-7,83|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,13-7,85|Postcondition
//::   calls: []
//::
