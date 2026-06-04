method Abs(x: int) returns (y: int)
  ensures 4 == 4
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x; // _USECASE_no_postconditions.dfy(4,5)-(4,12): assignment (or return)
  } else {
    y :=  Id(x); // _USECASE_no_postconditions.dfy(6,5)-(6,11): assignment (or return)
  }
}

function Id<T> (a : T) : T {
    a
}



//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 2
//::       col: 11
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 5122
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 3
//::       col: 20
//::     end:
//::       line: 3
//::       col: 23
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 5501
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 24
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 5580
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 7
//::       col: 5
//::     end:
//::       line: 7
//::       col: 12
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 16
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 11
//::       col: 1
//::     end:
//::       line: 11
//::       col: 1
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
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
//::   - locationId: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|13,1-15,1
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 13
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - function definition for Id
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23
//::       provers:
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|13,1-15,1
//::     - top: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24
//::       provers:
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12
//::   proofUnused:
//::     - top: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16
//::       unused:
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1
//::     - top: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23
//::       unused:
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1
//::     - top: snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24
//::       unused:
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16
//::         - snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1
//::   connections: []
//::
