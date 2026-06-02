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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,9
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 9
//::     methodName: IsEven
//::     methodType: well-formedness
//::     prooftexts:
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3302
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,14
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 14
//::     methodName: IsEven
//::     methodType: well-formedness
//::     prooftexts:
//::       - function call result
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 10
//::       col: 14
//::     end:
//::       line: 10
//::       col: 14
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 6512
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 13
//::     end:
//::       line: 7
//::       col: 85
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 13781
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 19
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 33
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 24
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 11641
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 11
//::       col: 24
//::     end:
//::       line: 11
//::       col: 33
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 11741
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 19
//::     end:
//::       line: 12
//::       col: 19
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 80
//::     end:
//::       line: 12
//::       col: 85
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 10560
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 12
//::       col: 19
//::     end:
//::       line: 12
//::       col: 87
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 15725
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 14
//::       col: 33
//::     end:
//::       line: 14
//::       col: 38
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 10285
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 16
//::       col: 13
//::     end:
//::       line: 16
//::       col: 28
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 20
//::       col: 1
//::     end:
//::       line: 20
//::       col: 1
//::     methodName: IsEvenAtIndexEven
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,78-7,83
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 78
//::     end:
//::       line: 7
//::       col: 83
//::     methodName: IsEvenAtIndexEven
//::     methodType: well-formedness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 8727
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,13-7,85
//::     file: snapshot_bug_predicate_body_uncovered.dfy
//::     start:
//::       line: 7
//::       col: 13
//::     end:
//::       line: 7
//::       col: 85
//::     methodName: IsEvenAtIndexEven
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::       provers:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::       provers:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::       provers:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::   proofUnused:
//::     - top: snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,9
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEven|well-formedness|3,5-3,14
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|14,33-14,38
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|7,13-7,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|9,5-9,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|10,14-10,14
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,19-11,24
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|11,24-11,33
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,19
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,80-12,85
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|12,19-12,87
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|16,13-16,28
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|correctness|20,1-20,1
//::     - top: >-
//::         snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,78-7,83
//::       unused:
//::         - >-
//::           snapshot_bug_predicate_body_uncovered.dfy|IsEvenAtIndexEven|well-formedness|7,13-7,85
//::   connections: []
//::
