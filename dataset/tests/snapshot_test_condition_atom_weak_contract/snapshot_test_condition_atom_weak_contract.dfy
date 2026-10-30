// The contract does not fix the sign of r, so the test of x is unused.
method Abs(x: int) returns (r: int)
  ensures r * r == x * x
{
  if x < 0 {
    r := -x;
  } else {
    r := x;
  }
}

// Same code with the sign fixed: the test is needed.
method AbsFull(x: int) returns (r: int)
  ensures r >= 0 && r * r == x * x
{
  if x < 0 {
    r := -x;
  } else {
    r := x;
  }
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|3,11-3,24
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 24
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4201
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|6,5-6,12
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 12
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|8,5-8,11
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 11
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|5,6-5,10
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 5
//::       col: 6
//::     end:
//::       line: 5
//::       col: 10
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|10,1-10,1
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
//::       col: 1
//::     methodName: Abs
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
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,11-14,16
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 14
//::       col: 11
//::     end:
//::       line: 14
//::       col: 16
//::     methodName: AbsFull
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
//::       batchResourceCount: 4168
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|16,6-16,10
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 16
//::       col: 6
//::     end:
//::       line: 16
//::       col: 10
//::     methodName: AbsFull
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|17,5-17,12
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 17
//::       col: 5
//::     end:
//::       line: 17
//::       col: 12
//::     methodName: AbsFull
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|19,5-19,11
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 19
//::       col: 5
//::     end:
//::       line: 19
//::       col: 11
//::     methodName: AbsFull
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,21-14,34
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 14
//::       col: 21
//::     end:
//::       line: 14
//::       col: 34
//::     methodName: AbsFull
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 4931
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|21,1-21,1
//::     file: snapshot_test_condition_atom_weak_contract.dfy
//::     start:
//::       line: 21
//::       col: 1
//::     end:
//::       line: 21
//::       col: 1
//::     methodName: AbsFull
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'r', which is subject to definite-assignment rules, is
//::         always initialized at this return point
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
//::     - top: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|3,11-3,24
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|6,5-6,12
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|8,5-8,11
//::     - top: >-
//::         snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,11-14,16
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|16,6-16,10
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|17,5-17,12
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|19,5-19,11
//::     - top: >-
//::         snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,21-14,34
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|17,5-17,12
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|19,5-19,11
//::   proofUnused:
//::     - top: snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|3,11-3,24
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|5,6-5,10
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|Abs|correctness|10,1-10,1
//::     - top: >-
//::         snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,11-14,16
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,21-14,34
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|21,1-21,1
//::     - top: >-
//::         snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,21-14,34
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|14,11-14,16
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|16,6-16,10
//::         - >-
//::           snapshot_test_condition_atom_weak_contract.dfy|AbsFull|correctness|21,1-21,1
//::   connections: []
//::
