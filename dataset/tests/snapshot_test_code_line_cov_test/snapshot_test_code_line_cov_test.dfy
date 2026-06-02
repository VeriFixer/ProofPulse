method ret32(a: int) returns (x:int)
{
    x := 32;
    assert(x == 32);
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,20
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 20
//::     methodName: ret32
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
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3363
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_code_line_cov_test.dfy|ret32|correctness|3,5-3,12
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
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
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,12-4,12
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 12
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'x', which is subject to definite-assignment rules, is always
//::         initialized here
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_code_line_cov_test.dfy|ret32|correctness|5,1-5,1
//::     file: snapshot_test_code_line_cov_test.dfy
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
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,20
//::       provers:
//::         - snapshot_test_code_line_cov_test.dfy|ret32|correctness|3,5-3,12
//::   proofUnused:
//::     - top: snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,20
//::       unused:
//::         - snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,12-4,12
//::         - snapshot_test_code_line_cov_test.dfy|ret32|correctness|5,1-5,1
//::   connections: []
//::
