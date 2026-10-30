method Div(a: int, b: int) returns (q: int)
  requires b > 0
  ensures q == a / b
{
  if b != 0 {
    q := a / b;
  } else {
    q := 0;
  }
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|3,11-3,20
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 20
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4539
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|2,12-2,16
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Precondition
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|5,6-5,11
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 5
//::       col: 6
//::     end:
//::       line: 5
//::       col: 11
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Condition
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,5-6,15
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 15
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,10-6,14
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 6
//::       col: 10
//::     end:
//::       line: 6
//::       col: 14
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 3091
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|8,5-8,11
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 11
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
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
//::   - locationId: snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|10,1-10,1
//::     file: snapshot_test_condition_atom_defensive_check.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
//::       col: 1
//::     methodName: Div
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'q', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'q', which is subject to definite-assignment rules, is
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
//::         snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|3,11-3,20
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|5,6-5,11
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,5-6,15
//::     - top: >-
//::         snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,10-6,14
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|5,6-5,11
//::   proofUnused:
//::     - top: >-
//::         snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|3,11-3,20
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,10-6,14
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|8,5-8,11
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|10,1-10,1
//::     - top: >-
//::         snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,10-6,14
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|6,5-6,15
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|8,5-8,11
//::         - >-
//::           snapshot_test_condition_atom_defensive_check.dfy|Div|correctness|10,1-10,1
//::   connections: []
//::
