method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := 32 + 1;
}

method Main(){
    var b := ret32(32);
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_pre_cov_test.dfy|ret32|correctness|3,13-3,21
//::     file: snapshot_test_pre_cov_test.dfy
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3484
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_pre_cov_test.dfy|ret32|correctness|5,5-5,16
//::     file: snapshot_test_pre_cov_test.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 16
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
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_pre_cov_test.dfy|ret32|correctness|2,14-2,19
//::     file: snapshot_test_pre_cov_test.dfy
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
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_pre_cov_test.dfy|ret32|correctness|6,1-6,1
//::     file: snapshot_test_pre_cov_test.dfy
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
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_pre_cov_test.dfy|Main|correctness|9,9-9,23
//::     file: snapshot_test_pre_cov_test.dfy
//::     start:
//::       line: 9
//::       col: 9
//::     end:
//::       line: 9
//::       col: 23
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - the precondition always holds
//::       - requires clause at snapshot_test_pre_cov_test.dfy(2,14)-(2,19) from call
//::       - call
//::       - assignment (or return)
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3312
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_pre_cov_test.dfy|Main|correctness|2,14-2,19
//::     file: snapshot_test_pre_cov_test.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Precondition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_pre_cov_test.dfy|ret32|correctness|3,13-3,21
//::       provers:
//::         - snapshot_test_pre_cov_test.dfy|ret32|correctness|5,5-5,16
//::   proofUnused:
//::     - top: snapshot_test_pre_cov_test.dfy|ret32|correctness|3,13-3,21
//::       unused:
//::         - snapshot_test_pre_cov_test.dfy|ret32|correctness|2,14-2,19
//::         - snapshot_test_pre_cov_test.dfy|ret32|correctness|6,1-6,1
//::     - top: snapshot_test_pre_cov_test.dfy|Main|correctness|9,9-9,23
//::       unused:
//::         - snapshot_test_pre_cov_test.dfy|Main|correctness|9,9-9,23
//::   connections:
//::     - call: snapshot_test_pre_cov_test.dfy|Main|correctness|9,9-9,23
//::       targets:
//::         - snapshot_test_pre_cov_test.dfy|Main|correctness|2,14-2,19
//::
