method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := x; // Line never covered bug report opened
  }
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,21-2,21|Postcondition
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 2
//::       col: 21
//::     end:
//::       line: 2
//::       col: 21
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23|Postcondition
//::     file: snapshot_bug_assigment_never_covered.dfy
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
//::       snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24|Postcondition
//::     file: snapshot_bug_assigment_never_covered.dfy
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
//::   - id: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12|CodeLine
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11|CodeLine
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 11
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1|AssertionAutomatic
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
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
//::       snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,22-3,22|Postcondition
//::     file: snapshot_bug_assigment_never_covered.dfy
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
//::         snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,21-2,21|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24|Postcondition
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12|CodeLine
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11|CodeLine
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,22-3,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24|Postcondition
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23|Postcondition
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11|CodeLine
//::         - >-
//::           snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1|AssertionAutomatic
//::   calls: []
//::
