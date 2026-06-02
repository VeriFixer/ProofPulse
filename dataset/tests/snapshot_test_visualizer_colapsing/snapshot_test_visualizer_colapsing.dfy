method Abs(x: int) returns (y: int)
  requires 0 <= x <= 10
  ensures y >= 10
{
  return x + 20;
}
//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,11-3,16
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 16
//::     methodName: Abs
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
//::       batchResourceCount: 3878
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,12-2,17
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 17
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 16
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,17-2,22
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 2
//::       col: 17
//::     end:
//::       line: 2
//::       col: 22
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|6,1-6,1
//::     file: snapshot_test_visualizer_colapsing.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
//::       col: 1
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,11-3,16
//::       provers:
//::         - snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,12-2,17
//::         - snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16
//::   proofUnused:
//::     - top: snapshot_test_visualizer_colapsing.dfy|Abs|correctness|3,11-3,16
//::       unused:
//::         - snapshot_test_visualizer_colapsing.dfy|Abs|correctness|2,17-2,22
//::         - snapshot_test_visualizer_colapsing.dfy|Abs|correctness|5,3-5,16
//::         - snapshot_test_visualizer_colapsing.dfy|Abs|correctness|6,1-6,1
//::   connections: []
//::
