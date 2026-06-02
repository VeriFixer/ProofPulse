method ret32(a: int) returns (x:int)
{
    x := 32;
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_code_line_unc.dfy|ret32|correctness|4,1-4,1
//::     file: snapshot_test_code_line_unc.dfy
//::     start:
//::       line: 4
//::       col: 1
//::     end:
//::       line: 4
//::       col: 1
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'x', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'x', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3411
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_code_line_unc.dfy|ret32|correctness|3,5-3,12
//::     file: snapshot_test_code_line_unc.dfy
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
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy: []
//::   proofUnused:
//::     - top: snapshot_test_code_line_unc.dfy|ret32|correctness|4,1-4,1
//::       unused:
//::         - snapshot_test_code_line_unc.dfy|ret32|correctness|3,5-3,12
//::   connections: []
//::
