method ret32(a : int) returns (x:int)
    requires a == 32
    ensures x==32 + 1
{
    x := 32 + 1;
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: snapshot_test_pre_unc.dfy|ret32|correctness|3,14-3,14|Postcondition
//::     file: snapshot_test_pre_unc.dfy
//::     start:
//::       line: 3
//::       col: 14
//::     end:
//::       line: 3
//::       col: 14
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_pre_unc.dfy|ret32|correctness|3,13-3,21|Postcondition
//::     file: snapshot_test_pre_unc.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 21
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_pre_unc.dfy|ret32|correctness|5,5-5,16|CodeLine
//::     file: snapshot_test_pre_unc.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 16
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_pre_unc.dfy|ret32|correctness|2,14-2,19|Precondition
//::     file: snapshot_test_pre_unc.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: snapshot_test_pre_unc.dfy|ret32|correctness|6,1-6,1|AssertionAutomatic
//::     file: snapshot_test_pre_unc.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
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
//::     - id: snapshot_test_pre_unc.dfy|ret32|correctness|3,14-3,14|Postcondition
//::       provedBy:
//::         - snapshot_test_pre_unc.dfy|ret32|correctness|3,13-3,21|Postcondition
//::         - snapshot_test_pre_unc.dfy|ret32|correctness|5,5-5,16|CodeLine
//::       proofUnused:
//::         - snapshot_test_pre_unc.dfy|ret32|correctness|2,14-2,19|Precondition
//::         - snapshot_test_pre_unc.dfy|ret32|correctness|6,1-6,1|AssertionAutomatic
//::   calls: []
//::
