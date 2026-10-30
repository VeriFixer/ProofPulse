ghost predicate P(x: int)
ghost function F(x: int): int
ghost function G(x: int): int

// z3's core holds only the second precondition and the postcondition. The
// term F(a) that triggers the second precondition is created by instantiating
// the first one on G(a), which the third precondition supplies. Removing the
// first or the third precondition breaks the postcondition.
method Chain(a: int)
  requires forall x {:trigger G(x)} :: F(x) == G(x) + 1
  requires forall x {:trigger F(x)} :: P(x)
  requires G(a) > 0
  ensures P(a)
{
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_trigger_chain.dfy|Chain|correctness|13,11-13,14
//::     file: snapshot_test_trigger_chain.dfy
//::     start:
//::       line: 13
//::       col: 11
//::     end:
//::       line: 13
//::       col: 14
//::     methodName: Chain
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
//::       batchResourceCount: 3675
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_trigger_chain.dfy|Chain|correctness|10,12-10,55
//::     file: snapshot_test_trigger_chain.dfy
//::     start:
//::       line: 10
//::       col: 12
//::     end:
//::       line: 10
//::       col: 55
//::     methodName: Chain
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
//::   - locationId: snapshot_test_trigger_chain.dfy|Chain|correctness|11,12-11,43
//::     file: snapshot_test_trigger_chain.dfy
//::     start:
//::       line: 11
//::       col: 12
//::     end:
//::       line: 11
//::       col: 43
//::     methodName: Chain
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
//::   - locationId: snapshot_test_trigger_chain.dfy|Chain|correctness|12,12-12,19
//::     file: snapshot_test_trigger_chain.dfy
//::     start:
//::       line: 12
//::       col: 12
//::     end:
//::       line: 12
//::       col: 19
//::     methodName: Chain
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
//::     - top: snapshot_test_trigger_chain.dfy|Chain|correctness|13,11-13,14
//::       provers:
//::         - snapshot_test_trigger_chain.dfy|Chain|correctness|10,12-10,55
//::         - snapshot_test_trigger_chain.dfy|Chain|correctness|11,12-11,43
//::         - snapshot_test_trigger_chain.dfy|Chain|correctness|12,12-12,19
//::   proofUnused: []
//::   connections: []
//::
