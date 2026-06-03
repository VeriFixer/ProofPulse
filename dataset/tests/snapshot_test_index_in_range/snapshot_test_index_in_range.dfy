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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 6484
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: zeroVector
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
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
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
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 14201
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     methodName: zeroVector
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
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 15214
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 14
//::     methodName: zeroVector
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
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 28
//::     methodName: zeroVector
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
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 15
//::     methodName: zeroVector
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
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 29
//::     end:
//::       line: 9
//::       col: 31
//::     methodName: zeroVector
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
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 13126
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 31
//::     methodName: zeroVector
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
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 24
//::     methodName: zeroVector
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
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 15764
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 9
//::       col: 24
//::     end:
//::       line: 9
//::       col: 31
//::     methodName: zeroVector
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
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 15944
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 49
//::     end:
//::       line: 10
//::       col: 49
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 18
//::       batchOutcome: Valid
//::       batchResourceCount: 14196
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 49
//::     end:
//::       line: 10
//::       col: 53
//::     methodName: zeroVector
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
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 14782
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 58
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
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
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
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
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 20254
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 17
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 15017
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 9
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 14348
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 13
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 14868
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 12
//::       col: 9
//::     end:
//::       line: 12
//::       col: 19
//::     methodName: zeroVector
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
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 19
//::     methodName: zeroVector
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
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 14
//::       col: 5
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 15574
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     file: snapshot_test_index_in_range.dfy
//::     start:
//::       line: 15
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
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
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::       provers:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::   proofUnused:
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|13,9-13,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::     - top: snapshot_test_index_in_range.dfy|zeroVector|correctness|8,5-14,5
//::       unused:
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|2,13-2,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|3,13-3,59
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|5,9-5,14
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,19-6,21
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|6,5-6,28
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|7,9-7,15
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,29-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,19-9,24
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|9,24-9,31
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,49
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,49-10,53
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|10,19-10,58
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|8,15-8,17
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,9
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,13
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|12,9-12,19
//::         - snapshot_test_index_in_range.dfy|zeroVector|correctness|15,1-15,1
//::   connections: []
//::
