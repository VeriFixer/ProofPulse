method ret32(a: int) returns (x:int)
{
    x := 32;
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_code_line_unc.dfy|ret32|correctness|4,1-4,1|AssertionAutomatic
//::     file: snapshot_test_code_line_unc.dfy
//::     start:
//::       line: 4
//::       col: 1
//::     end:
//::       line: 4
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'x', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_code_line_unc.dfy|ret32|correctness|3,5-3,12|CodeLine
//::     file: snapshot_test_code_line_unc.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_code_line_unc.dfy|ret32|correctness|4,1-4,1|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_code_line_unc.dfy|ret32|correctness|4,1-4,1|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_code_line_unc.dfy|ret32|correctness|3,5-3,12|CodeLine
//::   calls: []
//::
