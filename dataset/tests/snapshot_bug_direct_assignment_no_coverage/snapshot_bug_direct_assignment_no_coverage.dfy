method Max(a: int, b: int) returns (max: int)
    ensures max >= a && max >= b
    ensures max == a || max == b
{
    if a >= b {
        max := a;
    } else {
        max := b;
    }
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 20
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3485
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 17
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 17
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 25
//::     end:
//::       line: 2
//::       col: 32
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 3665
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 32
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 3795
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
//::       col: 1
//::     methodName: Max
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'max', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'max', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'max', which is subject to definite-assignment rules, is
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
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20
//::       provers:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32
//::       provers:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32
//::       provers:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17
//::   proofUnused:
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20
//::       unused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32
//::       unused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1
//::     - top: snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32
//::       unused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1
//::   connections: []
//::
