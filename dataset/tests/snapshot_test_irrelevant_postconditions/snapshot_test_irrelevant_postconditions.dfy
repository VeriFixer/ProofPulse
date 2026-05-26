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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,13-2,13|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 2
//::       col: 11
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 3
//::       col: 20
//::     end:
//::       line: 3
//::       col: 23
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 24
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12|CodeLine
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 7
//::       col: 5
//::     end:
//::       line: 7
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16|CodeLine
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 9
//::       col: 5
//::     end:
//::       line: 9
//::       col: 16
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1|AssertionAutomatic
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 11
//::       col: 1
//::     end:
//::       line: 11
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'y', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,21-3,21|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 3
//::       col: 21
//::     end:
//::       line: 3
//::       col: 21
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|13,1-15,1|CodeLine
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 13
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     prooftext: function definition for Id
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,22-4,22|Postcondition
//::     file: snapshot_test_irrelevant_postconditions.dfy
//::     start:
//::       line: 4
//::       col: 22
//::     end:
//::       line: 4
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,13-2,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12|CodeLine
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16|CodeLine
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,21-3,21|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16|CodeLine
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|13,1-15,1|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12|CodeLine
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,22-4,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|4,19-4,24|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|7,5-7,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|2,11-2,16|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|3,20-3,23|Postcondition
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|9,5-9,16|CodeLine
//::         - >-
//::           snapshot_test_irrelevant_postconditions.dfy|Abs|correctness|11,1-11,1|AssertionAutomatic
//::   calls: []
//::
