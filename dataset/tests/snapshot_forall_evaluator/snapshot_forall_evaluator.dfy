method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a.Length >= 0
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    for i := 0 to a.Length
        invariant result ==> forall k :: 0 <= k < i ==> a[k] == n
    {
        if a[i] != n {
            result := false;
            break;
        }
    }
}

method Main()
{
    var a := new int[1];
    a[0] := 5;
    var r := AllElementsEqual(a, 5);
    assert(r == true);

}

//:: method AllElementsEqual:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,16-2,16|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 26
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 45
//::     end:
//::       line: 3
//::       col: 47
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 36
//::     end:
//::       line: 3
//::       col: 47
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 58
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 36
//::     end:
//::       line: 3
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 14
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 46
//::     end:
//::       line: 4
//::       col: 48
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 37
//::     end:
//::       line: 4
//::       col: 48
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 58
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 66
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,59-4,59|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 59
//::     end:
//::       line: 4
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,48-4,48|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 48
//::     end:
//::       line: 4
//::       col: 48
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,59-3,59|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 59
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,47-3,47|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 47
//::     end:
//::       line: 3
//::       col: 47
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,21-7,21|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 26
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 66
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 66
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 19
//::     prooftext: >-
//::       variable 'result', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 57
//::     end:
//::       line: 8
//::       col: 57
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 57
//::     end:
//::       line: 8
//::       col: 60
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 65
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 30
//::     end:
//::       line: 8
//::       col: 65
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 10
//::       col: 12
//::     end:
//::       line: 10
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 10
//::       col: 12
//::     end:
//::       line: 10
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 11
//::       col: 13
//::     end:
//::       line: 11
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 15
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'result', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
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
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,30|LoopInvariant
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 30
//::     end:
//::       line: 8
//::       col: 30
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,13-10,13|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 10
//::       col: 13
//::     end:
//::       line: 10
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,24|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 24
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,25|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 25
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,58-8,58|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 58
//::     end:
//::       line: 8
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     assertionGroup: AllElementsEqual
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 19
//::       col: 22
//::     end:
//::       line: 19
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 19
//::       col: 22
//::     end:
//::       line: 19
//::       col: 22
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 14
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|CodeLine
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 21
//::       col: 9
//::     end:
//::       line: 21
//::       col: 36
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22|AssertionManual
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 22
//::       col: 5
//::     end:
//::       line: 22
//::       col: 22
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_forall_evaluator.dfy|Main|correctness|20,6-20,6|AssertionAutomatic
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 6
//::     end:
//::       line: 20
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|21,30-21,30|Precondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 21
//::       col: 30
//::     end:
//::       line: 21
//::       col: 30
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|Call
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 21
//::       col: 9
//::     end:
//::       line: 21
//::       col: 36
//::     prooftext: requires clause at snapshot_forall_evaluator.dfy(2,14)-(2,26) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|2,14-2,26|Precondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 26
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,5|AssertionManual
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 22
//::       col: 5
//::     end:
//::       line: 22
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_forall_evaluator.dfy|Main|correctness|4,25-4,66|Postcondition
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 66
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,16-2,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,59-4,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,48-4,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,59-3,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,47-3,47|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,45-3,47|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,16|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,13|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,47|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,58-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,36-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|3,13-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,14|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,46-4,48|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,37-4,48|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,58|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,61|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,58-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|well-formedness|4,13-4,66|Postcondition
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,21-7,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,30|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,13-10,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,24|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,25|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,58-8,58|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26|Precondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66|Postcondition
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65|LoopInvariant
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|AssertionAutomatic
//::       provedBy:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|CodeLine
//::       proofUnused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22|AssertionManual
//::     - id: >-
//::         snapshot_forall_evaluator.dfy|Main|correctness|20,6-20,6|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22|AssertionManual
//::     - id: snapshot_forall_evaluator.dfy|Main|correctness|21,30-21,30|Precondition
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|Call
//::       proofUnused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22|AssertionManual
//::     - id: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|Call
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22|AssertionManual
//::       proofUnused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22|CodeLine
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24|CodeLine
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5|AssertionAutomatic
//::         - >-
//::           snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8|AssertionAutomatic
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|CodeLine
//::   calls:
//::     - id: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36|Call
//::       connections:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|2,14-2,26|Precondition
//::         - snapshot_forall_evaluator.dfy|Main|correctness|4,25-4,66|Postcondition
//::
