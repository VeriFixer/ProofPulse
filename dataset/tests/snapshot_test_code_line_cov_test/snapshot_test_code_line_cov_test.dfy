method ret32(a: int) returns (x:int)
{
    x := 32;
    assert(x == 32);
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,5|AssertionManual
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_code_line_cov_test.dfy|ret32|correctness|3,5-3,12|CodeLine
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,20|AssertionManual
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,12-4,12|AssertionAutomatic
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: >-
//::       variable 'x', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_code_line_cov_test.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     file: snapshot_test_code_line_cov_test.dfy
//::     start:
//::       line: 5
//::       col: 1
//::     end:
//::       line: 5
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'x', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_code_line_cov_test.dfy|ret32|correctness|3,5-3,12|CodeLine
//::         - >-
//::           snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,5-4,20|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_code_line_cov_test.dfy|ret32|correctness|4,12-4,12|AssertionAutomatic
//::         - >-
//::           snapshot_test_code_line_cov_test.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::   calls: []
//::
