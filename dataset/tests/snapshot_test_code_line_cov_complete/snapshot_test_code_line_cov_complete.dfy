method ret32(a: int) returns (x:int)
    ensures x==32 
{
    x := 32;
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_code_line_cov_complete.dfy|ret32|correctness|2,13-2,16
//::     file: snapshot_test_code_line_cov_complete.dfy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_code_line_cov_complete.dfy|ret32|correctness|4,5-4,12
//::     file: snapshot_test_code_line_cov_complete.dfy
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
//::   - locationId: snapshot_test_code_line_cov_complete.dfy|ret32|correctness|5,1-5,1
//::     file: snapshot_test_code_line_cov_complete.dfy
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_code_line_cov_complete.dfy|ret32|correctness|2,13-2,16
//::       provers:
//::         - snapshot_test_code_line_cov_complete.dfy|ret32|correctness|4,5-4,12
//::   proofUnused:
//::     - top: snapshot_test_code_line_cov_complete.dfy|ret32|correctness|2,13-2,16
//::       unused:
//::         - snapshot_test_code_line_cov_complete.dfy|ret32|correctness|5,1-5,1
//::   connections: []
//::
