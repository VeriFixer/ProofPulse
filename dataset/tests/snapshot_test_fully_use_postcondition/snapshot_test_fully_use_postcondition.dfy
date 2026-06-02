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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,13-2,16
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3363
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|ret32|correctness|4,5-4,12
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|ret32|correctness|5,1-5,1
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,17
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 17
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
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4460
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19
//::     file: snapshot_test_fully_use_postcondition.dfy
//::     start:
//::       line: 7
//::       col: 6
//::     end:
//::       line: 7
//::       col: 19
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - >-
//::         ensures clause at snapshot_test_fully_use_postcondition.dfy(2,13)-(2,16)
//::         from call
//::       - call
//::     roles:
//::       isTop: false
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_fully_use_postcondition.dfy|Main|correctness|2,13-2,16
//::     file: snapshot_test_fully_use_postcondition.dfy
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
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,13-2,16
//::       provers:
//::         - snapshot_test_fully_use_postcondition.dfy|ret32|correctness|4,5-4,12
//::     - top: snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,17
//::       provers:
//::         - snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19
//::   proofUnused:
//::     - top: snapshot_test_fully_use_postcondition.dfy|ret32|correctness|2,13-2,16
//::       unused:
//::         - snapshot_test_fully_use_postcondition.dfy|ret32|correctness|5,1-5,1
//::     - top: snapshot_test_fully_use_postcondition.dfy|Main|correctness|8,5-8,17
//::       unused:
//::         - snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19
//::   connections:
//::     - call: snapshot_test_fully_use_postcondition.dfy|Main|correctness|7,6-7,19
//::       targets:
//::         - snapshot_test_fully_use_postcondition.dfy|Main|correctness|2,13-2,16
//::
