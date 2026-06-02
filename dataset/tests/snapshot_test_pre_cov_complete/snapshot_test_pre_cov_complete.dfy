method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := a+1;
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_pre_cov_complete.dfy|ret32|correctness|3,13-3,21
//::     file: snapshot_test_pre_cov_complete.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 21
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3648
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_pre_cov_complete.dfy|ret32|correctness|2,14-2,19
//::     file: snapshot_test_pre_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_pre_cov_complete.dfy|ret32|correctness|5,5-5,13
//::     file: snapshot_test_pre_cov_complete.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 13
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_test_pre_cov_complete.dfy|ret32|correctness|6,1-6,1
//::     file: snapshot_test_pre_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
//::       col: 1
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'x', which is subject to definite-assignment rules, is
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
//::     - top: snapshot_test_pre_cov_complete.dfy|ret32|correctness|3,13-3,21
//::       provers:
//::         - snapshot_test_pre_cov_complete.dfy|ret32|correctness|2,14-2,19
//::         - snapshot_test_pre_cov_complete.dfy|ret32|correctness|5,5-5,13
//::   proofUnused:
//::     - top: snapshot_test_pre_cov_complete.dfy|ret32|correctness|3,13-3,21
//::       unused:
//::         - snapshot_test_pre_cov_complete.dfy|ret32|correctness|6,1-6,1
//::   connections: []
//::
