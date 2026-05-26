method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  assert(43 == 43); 

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}



//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,3|AssertionManual
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 3
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19|AssertionManual
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 19
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23|Postcondition
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 2
//::       col: 20
//::     end:
//::       line: 2
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24|Postcondition
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 3
//::       col: 19
//::     end:
//::       line: 3
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12|CodeLine
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15|CodeLine
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1|AssertionAutomatic
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 12
//::       col: 1
//::     end:
//::       line: 12
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,21-2,21|Postcondition
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 2
//::       col: 21
//::     end:
//::       line: 2
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|14,1-16,1|CodeLine
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 16
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
//::       snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,22-3,22|Postcondition
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 3
//::       col: 22
//::     end:
//::       line: 3
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
//::         snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,3|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12|CodeLine
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15|CodeLine
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,21-2,21|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15|CodeLine
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|14,1-16,1|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19|AssertionManual
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12|CodeLine
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,22-3,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23|Postcondition
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19|AssertionManual
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15|CodeLine
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1|AssertionAutomatic
//::   calls: []
//::
