method ret32(a: int) returns (x:int)
    ensures x==32 
{
    x := 32;
}
method Main() {
	var n := ret32(5);
    assert n==32;
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,14-2,14|Postcondition
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::       snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,13-2,16|Postcondition
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::   - id: >-
//::       snapshot_test_fully_use_postcondition.dfy|ret32|correctness|4,5-4,12|CodeLine
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::       snapshot_test_fully_use_postcondition.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::       snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,5|AssertionManual
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19|Call
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 7
//::       col: 6
//::     end:
//::       line: 7
//::       col: 19
//::     prooftext: >-
//::       ensures clause at snapshot_test_fully_use_postcondition.dfy(2,13)-(2,16)
//::       from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_test_fully_use_postcondition.dfy|Main|correctness|2,13-2,16|Postcondition
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::       snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,17|AssertionManual
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Main
//::     methodType: correctness
//::     assertionGroup: Main
//::   - id: >-
//::       snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19|CodeLine
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 7
//::       col: 6
//::     end:
//::       line: 7
//::       col: 19
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
//::         snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,14-2,14|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,13-2,16|Postcondition
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|ret32|correctness|4,5-4,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|ret32|correctness|5,1-5,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19|Call
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,17|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19|CodeLine
//::   calls:
//::     - id: snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19|Call
//::       connections:
//::         - >-
//::           snapshot_test_fully_use_postcondition.dfy|Main|correctness|2,13-2,16|Postcondition
//::
