method Abs(x: int) returns (y: int)
  requires 0 <= x <= 10
  ensures y >= 10
{
  return x + 20;
}
//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,13-3,13|Postcondition
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,12-2,17|Precondition
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 17
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,11-3,16|Postcondition
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 16
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16|CodeLine
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
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
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,17-2,22|Precondition
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 2
//::       col: 17
//::     end:
//::       line: 2
//::       col: 22
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Abs
//::     methodType: correctness
//::     assertionGroup: Abs
//::   - id: >-
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16|AssertionAutomatic
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 16
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
//::       snapshot_test_visualizer_colapsing.dfy|Abs|correctness|6,1-6,1|AssertionAutomatic
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
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
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,13-3,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,12-2,17|Precondition
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,11-3,16|Postcondition
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,17-2,22|Precondition
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_visualizer_colapsing.dfy|Abs|correctness|6,1-6,1|AssertionAutomatic
//::   calls: []
//::
