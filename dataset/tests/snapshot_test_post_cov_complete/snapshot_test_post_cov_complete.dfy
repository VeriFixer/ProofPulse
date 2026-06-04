method ret32() returns (x:int)
    ensures x==32
{
    x := 32;
}

method Main(){
    var b := ret32();
    assert(b == 32);
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_post_cov_complete.dfy|ret32|correctness|2,13-2,16
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
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
//::       batchResourceCount: 3363
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_post_cov_complete.dfy|ret32|correctness|4,5-4,12
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 12
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
//::   - locationId: snapshot_test_post_cov_complete.dfy|ret32|correctness|5,1-5,1
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 5
//::       col: 1
//::     end:
//::       line: 5
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
//::   - locationId: snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,20
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 20
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionManual
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4398
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 21
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - >-
//::         ensures clause at snapshot_test_post_cov_complete.dfy(2,13)-(2,16) from
//::         call
//::       - call
//::     roles:
//::       isTop: false
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_post_cov_complete.dfy|Main|correctness|2,13-2,16
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_post_cov_complete.dfy|ret32|correctness|2,13-2,16
//::       provers:
//::         - snapshot_test_post_cov_complete.dfy|ret32|correctness|4,5-4,12
//::     - top: snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,20
//::       provers:
//::         - snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21
//::   proofUnused:
//::     - top: snapshot_test_post_cov_complete.dfy|ret32|correctness|2,13-2,16
//::       unused:
//::         - snapshot_test_post_cov_complete.dfy|ret32|correctness|5,1-5,1
//::     - top: snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,20
//::       unused:
//::         - snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21
//::   connections:
//::     - call: snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21
//::       targets:
//::         - snapshot_test_post_cov_complete.dfy|Main|correctness|2,13-2,16
//::
