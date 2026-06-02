method ret32(a: int)
{
    assert(1 == 1);
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_assert_cov_unc.dfy|ret32|correctness|3,5-3,19
//::     file: snapshot_test_assert_cov_unc.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 19
//::     methodName: ret32
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: AssertionManual
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3236
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy: []
//::   proofUnused: []
//::   connections: []
//::
