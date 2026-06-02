method swap(a : int, b:int) returns (c:int, d:int)
    ensures a + 1 == c
    ensures b + 1 == d
{
    c,d := a + 1,b + 1; // line appears uncovered but if split in two assigment it is covered
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 22
//::     methodName: swap
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3408
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 23
//::     methodName: swap
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 22
//::     methodName: swap
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 3597
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
//::       col: 1
//::     methodName: swap
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'd', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'd', which is subject to definite-assignment rules, is
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
//::     - top: snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22
//::       provers:
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23
//::     - top: snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22
//::       provers:
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23
//::   proofUnused:
//::     - top: snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22
//::       unused:
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1
//::     - top: snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22
//::       unused:
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23
//::         - snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1
//::   connections: []
//::
