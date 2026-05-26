method ret32(a: int)
{
    assert(1 == 1);
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: snapshot_test_assert_cov_unc.dfy|ret32|correctness|3,5-3,5|AssertionManual
//::     file: snapshot_test_assert_cov_unc.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//::   - id: >-
//::       snapshot_test_assert_cov_unc.dfy|ret32|correctness|3,5-3,19|AssertionManual
//::     file: snapshot_test_assert_cov_unc.dfy
//::     start:
//::       line: 3
//::       col: 5
//::     end:
//::       line: 3
//::       col: 19
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: ret32
//::     methodType: correctness
//::     assertionGroup: ret32
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_assert_cov_unc.dfy|ret32|correctness|3,5-3,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_unc.dfy|ret32|correctness|3,5-3,19|AssertionManual
//::       proofUnused: []
//::   calls: []
//::
