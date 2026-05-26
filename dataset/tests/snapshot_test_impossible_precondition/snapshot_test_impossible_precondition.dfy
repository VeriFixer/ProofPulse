method DemoImpossiblePrecondition(a: int)
    returns (r: int)
  requires forall t :: t*t + 1 <= t*t
  ensures 2 == 3
{
  var k := a + 1;
  var m := k * 2;
  r := m - k;
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,13-4,13|Postcondition
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|3,12-3,37|Precondition
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 3
//::       col: 12
//::     end:
//::       line: 3
//::       col: 37
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16|Postcondition
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 16
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|6,7-6,17|CodeLine
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 6
//::       col: 7
//::     end:
//::       line: 6
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|7,7-7,17|CodeLine
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 7
//::       col: 7
//::     end:
//::       line: 7
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|8,3-8,13|CodeLine
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 8
//::       col: 3
//::     end:
//::       line: 8
//::       col: 13
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//::   - id: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|9,1-9,1|AssertionAutomatic
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 9
//::       col: 1
//::     end:
//::       line: 9
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'r', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     assertionGroup: DemoImpossiblePrecondition
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,13-4,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|3,12-3,37|Precondition
//::       proofUnused:
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16|Postcondition
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|6,7-6,17|CodeLine
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|7,7-7,17|CodeLine
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|8,3-8,13|CodeLine
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|9,1-9,1|AssertionAutomatic
//::   calls: []
//::
