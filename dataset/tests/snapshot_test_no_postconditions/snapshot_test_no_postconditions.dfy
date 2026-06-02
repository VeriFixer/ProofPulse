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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_no_postconditions.dfy|Abs|correctness|8,1-8,1
//::     file: snapshot_test_no_postconditions.dfy
//::     start:
//::       line: 8
//::       col: 1
//::     end:
//::       line: 8
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4401
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_no_postconditions.dfy|Abs|correctness|4,5-4,12
//::     file: snapshot_test_no_postconditions.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 12
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_no_postconditions.dfy|Abs|correctness|6,5-6,15
//::     file: snapshot_test_no_postconditions.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 15
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy: []
//::   proofUnused:
//::     - top: snapshot_test_no_postconditions.dfy|Abs|correctness|8,1-8,1
//::       unused:
//::         - snapshot_test_no_postconditions.dfy|Abs|correctness|4,5-4,12
//::         - snapshot_test_no_postconditions.dfy|Abs|correctness|6,5-6,15
//::   connections: []
//::
