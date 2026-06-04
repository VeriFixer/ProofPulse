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
//:: version: 2
//:: nodes:
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 16
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3974
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|3,12-3,37
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 3
//::       col: 12
//::     end:
//::       line: 3
//::       col: 37
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Precondition
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|6,7-6,17
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 6
//::       col: 7
//::     end:
//::       line: 6
//::       col: 17
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|7,7-7,17
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 7
//::       col: 7
//::     end:
//::       line: 7
//::       col: 17
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|8,3-8,13
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 8
//::       col: 3
//::     end:
//::       line: 8
//::       col: 13
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|9,1-9,1
//::     file: snapshot_test_impossible_precondition.dfy
//::     start:
//::       line: 9
//::       col: 1
//::     end:
//::       line: 9
//::       col: 1
//::     methodName: DemoImpossiblePrecondition
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'r', which is subject to definite-assignment rules, is
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
//:: edges:
//::   provedBy:
//::     - top: >-
//::         snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16
//::       provers:
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|3,12-3,37
//::   proofUnused:
//::     - top: >-
//::         snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16
//::       unused:
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|4,11-4,16
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|6,7-6,17
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|7,7-7,17
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|8,3-8,13
//::         - >-
//::           snapshot_test_impossible_precondition.dfy|DemoImpossiblePrecondition|correctness|9,1-9,1
//::   connections: []
//::
