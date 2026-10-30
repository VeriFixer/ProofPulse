ghost predicate P(x: int)
ghost function F(x: int): int

// The assert is proved from the precondition, and its only part in the
// postcondition's proof is the term F(a), which triggers the quantifier.
method TriggerHint(a: int)
  requires forall x {:trigger F(x)} :: P(x) && F(x) > 0
  ensures P(a)
{
  assert F(a) > 0;
}

// The second precondition only supplies the term F(a).
method TriggerPrecondition(a: int)
  requires forall x {:trigger F(x)} :: P(x)
  requires F(a) > 0
  ensures P(a)
{
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|10,3-10,18
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 10
//::       col: 18
//::     methodName: TriggerHint
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionManual
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3569
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|7,12-7,55
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 7
//::       col: 12
//::     end:
//::       line: 7
//::       col: 55
//::     methodName: TriggerHint
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: Precondition
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|8,11-8,14
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 8
//::       col: 11
//::     end:
//::       line: 8
//::       col: 14
//::     methodName: TriggerHint
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
//::       batchResourceCount: 3694
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|17,11-17,14
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 17
//::       col: 11
//::     end:
//::       line: 17
//::       col: 14
//::     methodName: TriggerPrecondition
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
//::       batchResourceCount: 3235
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|15,12-15,43
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 15
//::       col: 12
//::     end:
//::       line: 15
//::       col: 43
//::     methodName: TriggerPrecondition
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
//::       snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|16,12-16,19
//::     file: snapshot_test_trigger_term_only.dfy
//::     start:
//::       line: 16
//::       col: 12
//::     end:
//::       line: 16
//::       col: 19
//::     methodName: TriggerPrecondition
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|10,3-10,18
//::       provers:
//::         - snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|7,12-7,55
//::     - top: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|8,11-8,14
//::       provers:
//::         - snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|7,12-7,55
//::         - snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|10,3-10,18
//::     - top: >-
//::         snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|17,11-17,14
//::       provers:
//::         - >-
//::           snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|15,12-15,43
//::         - >-
//::           snapshot_test_trigger_term_only.dfy|TriggerPrecondition|correctness|16,12-16,19
//::   proofUnused:
//::     - top: snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|10,3-10,18
//::       unused:
//::         - snapshot_test_trigger_term_only.dfy|TriggerHint|correctness|8,11-8,14
//::   connections: []
//::
