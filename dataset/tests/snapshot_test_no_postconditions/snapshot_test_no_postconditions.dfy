method Abs(x: int) returns (y: int)
{
  if x < 0 {
    y := -x; // _USECASE_no_postconditions.dfy(4,5)-(4,12): assignment (or return)
  } else {
    y := Id(x); // _USECASE_no_postconditions.dfy(6,5)-(6,11): assignment (or return)
  }
} //Note: As this is the only assertion that is added automatically it is really covered (in other tests with postcondiiton this assertion does not run)

function Id<T> (a : T) : T {
    a
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_no_postconditions.dfy|Abs|correctness|8,1-8,1|AssertionAutomatic
//::     file: snapshot_test_no_postconditions.dfy
//::     start:
//::       line: 8
//::       col: 1
//::     end:
//::       line: 8
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'y', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: snapshot_test_no_postconditions.dfy|Abs|correctness|4,5-4,12|CodeLine
//::     file: snapshot_test_no_postconditions.dfy
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
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: snapshot_test_no_postconditions.dfy|Abs|correctness|6,5-6,15|CodeLine
//::     file: snapshot_test_no_postconditions.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_no_postconditions.dfy|Abs|correctness|8,1-8,1|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_no_postconditions.dfy|Abs|correctness|8,1-8,1|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_test_no_postconditions.dfy|Abs|correctness|4,5-4,12|CodeLine
//::         - snapshot_test_no_postconditions.dfy|Abs|correctness|6,5-6,15|CodeLine
//::   calls: []
//::
