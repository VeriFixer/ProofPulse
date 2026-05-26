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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|ret32|correctness|2,14-2,14|Postcondition
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|ret32|correctness|2,13-2,16|Postcondition
//::     file: snapshot_test_post_cov_complete.dfy
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
//::   - id: snapshot_test_post_cov_complete.dfy|ret32|correctness|4,5-4,12|CodeLine
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     file: snapshot_test_post_cov_complete.dfy
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
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,5|AssertionManual
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21|Call
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 21
//::     prooftext: >-
//::       ensures clause at snapshot_test_post_cov_complete.dfy(2,13)-(2,16) from
//::       call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|Main|correctness|2,13-2,16|Postcondition
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,20|AssertionManual
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 20
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21|CodeLine
//::     file: snapshot_test_post_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 21
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_post_cov_complete.dfy|ret32|correctness|2,14-2,14|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_post_cov_complete.dfy|ret32|correctness|2,13-2,16|Postcondition
//::         - >-
//::           snapshot_test_post_cov_complete.dfy|ret32|correctness|4,5-4,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_post_cov_complete.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,5|AssertionManual
//::       provedBy:
//::         - snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21|Call
//::         - >-
//::           snapshot_test_post_cov_complete.dfy|Main|correctness|9,5-9,20|AssertionManual
//::       proofUnused:
//::         - snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21|CodeLine
//::   calls:
//::     - id: snapshot_test_post_cov_complete.dfy|Main|correctness|8,9-8,21|Call
//::       connections:
//::         - >-
//::           snapshot_test_post_cov_complete.dfy|Main|correctness|2,13-2,16|Postcondition
//::
