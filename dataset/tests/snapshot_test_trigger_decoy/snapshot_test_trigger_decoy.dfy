ghost predicate P(x: int)
ghost function F(x: int): int

// Both F(a) and F(a + 1) trigger the quantifier, but the postcondition only
// needs the instantiation on F(a): the third precondition can be removed.
method Decoy(a: int)
  requires forall x {:trigger F(x)} :: P(x)
  requires F(a) > 0
  requires F(a + 1) > 0
  ensures P(a)
{
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_trigger_decoy.dfy|Decoy|correctness|10,11-10,14
//::     file: snapshot_test_trigger_decoy.dfy
//::     start:
//::       line: 10
//::       col: 11
//::     end:
//::       line: 10
//::       col: 14
//::     methodName: Decoy
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
//::       batchResourceCount: 3447
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_trigger_decoy.dfy|Decoy|correctness|7,12-7,43
//::     file: snapshot_test_trigger_decoy.dfy
//::     start:
//::       line: 7
//::       col: 12
//::     end:
//::       line: 7
//::       col: 43
//::     methodName: Decoy
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
//::   - locationId: snapshot_test_trigger_decoy.dfy|Decoy|correctness|8,12-8,19
//::     file: snapshot_test_trigger_decoy.dfy
//::     start:
//::       line: 8
//::       col: 12
//::     end:
//::       line: 8
//::       col: 19
//::     methodName: Decoy
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
//::   - locationId: snapshot_test_trigger_decoy.dfy|Decoy|correctness|9,12-9,23
//::     file: snapshot_test_trigger_decoy.dfy
//::     start:
//::       line: 9
//::       col: 12
//::     end:
//::       line: 9
//::       col: 23
//::     methodName: Decoy
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_trigger_decoy.dfy|Decoy|correctness|10,11-10,14
//::       provers:
//::         - snapshot_test_trigger_decoy.dfy|Decoy|correctness|7,12-7,43
//::         - snapshot_test_trigger_decoy.dfy|Decoy|correctness|8,12-8,19
//::   proofUnused:
//::     - top: snapshot_test_trigger_decoy.dfy|Decoy|correctness|10,11-10,14
//::       unused:
//::         - snapshot_test_trigger_decoy.dfy|Decoy|correctness|9,12-9,23
//::   connections: []
//::
