method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall k :: 0 <= k < i ==> a[k] == n
    {
        if a[i] != n {
            result := false;
            break;
        }
    }
}

// Lurking bug these two lines

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 58
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 12756
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 45
//::     end:
//::       line: 3
//::       col: 47
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 6850
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 36
//::     end:
//::       line: 3
//::       col: 47
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 58
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 8090
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 61
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 8415
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 58
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 36
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 14
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 46
//::     end:
//::       line: 4
//::       col: 48
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 12232
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 37
//::     end:
//::       line: 4
//::       col: 48
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 61
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 13128
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 58
//::     end:
//::       line: 4
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 21
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 5632
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 13219
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 13256
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 19
//::     methodName: AllElementsEqual
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
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 14
//::     methodName: AllElementsEqual
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 6709
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 8
//::       col: 29
//::     end:
//::       line: 8
//::       col: 31
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 10670
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 31
//::     methodName: AllElementsEqual
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 24
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
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
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 11913
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 8
//::       col: 24
//::     end:
//::       line: 8
//::       col: 31
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
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
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 12078
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 19
//::     methodName: AllElementsEqual
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 9
//::       col: 57
//::     end:
//::       line: 9
//::       col: 57
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 11571
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 9
//::       col: 57
//::     end:
//::       line: 9
//::       col: 60
//::     methodName: AllElementsEqual
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
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 11738
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 65
//::     methodName: AllElementsEqual
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 9
//::       col: 30
//::     end:
//::       line: 9
//::       col: 65
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
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
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 13337
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 11
//::       col: 12
//::     end:
//::       line: 11
//::       col: 12
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 11114
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 11
//::       col: 12
//::     end:
//::       line: 11
//::       col: 15
//::     methodName: AllElementsEqual
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
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 11235
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 12
//::       col: 13
//::     end:
//::       line: 12
//::       col: 28
//::     methodName: AllElementsEqual
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
//::   - locationId: snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     file: snapshot_bug_forall.dfy
//::     start:
//::       line: 16
//::       col: 1
//::     end:
//::       line: 16
//::       col: 1
//::     methodName: AllElementsEqual
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::       provers:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::       provers:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::       provers:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::       provers:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::       provers:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::   proofUnused:
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,37-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,61
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,13
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,45-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,47
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,61
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,58-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,36-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|3,13-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,46-4,48
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,58
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,58-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|well-formedness|4,13-4,66
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::     - top: snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,15
//::       unused:
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|2,14-2,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,29-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,19-8,24
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|8,24-8,31
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,19
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,57
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,57-9,60
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,19-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|9,30-9,65
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|11,12-11,12
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|12,13-12,28
//::         - snapshot_bug_forall.dfy|AllElementsEqual|correctness|16,1-16,1
//::   connections: []
//::
