method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists j :: 0 <= j < i && s[j] == k)
    {
        if s[i] == k {
            result := true;
            break;
        }
    }
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 5
//::       col: 14
//::     end:
//::       line: 5
//::       col: 14
//::     methodName: ContainsK
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
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 30
//::     methodName: ContainsK
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
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 12068
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 20
//::     methodName: ContainsK
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
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 31
//::     methodName: ContainsK
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
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 24
//::     methodName: ContainsK
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 9722
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 24
//::     end:
//::       line: 6
//::       col: 31
//::     methodName: ContainsK
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
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
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 9778
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 19
//::     methodName: ContainsK
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
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 58
//::     end:
//::       line: 7
//::       col: 61
//::     methodName: ContainsK
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
//::       batchResourceCount: 9683
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 67
//::     methodName: ContainsK
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 11526
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 9
//::       col: 12
//::     end:
//::       line: 9
//::       col: 15
//::     methodName: ContainsK
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
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 9243
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 10
//::       col: 13
//::     end:
//::       line: 10
//::       col: 27
//::     methodName: ContainsK
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
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 14
//::       col: 1
//::     methodName: ContainsK
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
//:: edges:
//::   provedBy:
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::       provers:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::       provers:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::   proofUnused:
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::     - top: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15
//::       unused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1
//::   connections: []
//::
