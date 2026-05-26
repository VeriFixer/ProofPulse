method ret32() returns (x:int)
    ensures 3==3
{
    x := 32;
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: snapshot_test_post_cov_unc.dfy|ret32|correctness|2,14-2,14|Postcondition
//::     file: snapshot_test_post_cov_unc.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_post_cov_unc.dfy|ret32|correctness|2,13-2,16|Postcondition
//::     file: snapshot_test_post_cov_unc.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_post_cov_unc.dfy|ret32|correctness|4,5-4,12|CodeLine
//::     file: snapshot_test_post_cov_unc.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_post_cov_unc.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     file: snapshot_test_post_cov_unc.dfy
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
//::     - id: snapshot_test_post_cov_unc.dfy|ret32|correctness|2,14-2,14|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_post_cov_unc.dfy|ret32|correctness|2,13-2,16|Postcondition
//::       proofUnused:
//::         - snapshot_test_post_cov_unc.dfy|ret32|correctness|4,5-4,12|CodeLine
//::         - >-
//::           snapshot_test_post_cov_unc.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::   calls: []
//::
