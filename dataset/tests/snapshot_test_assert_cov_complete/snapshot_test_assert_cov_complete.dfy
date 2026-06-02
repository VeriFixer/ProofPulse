method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  assert |B| == |B'| + 1; 
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B'; // Essential Assertion for prove
  }
}

// Limitations 
// Although comenting out assertion 8 still makes verification to pass it really is being 
// highlighted in the unsat core (even with minimize options, To improve further only with scripts)
// To even extract more minimal cores possibly. But for now is working
// Line 3 is covcomplete as it is needed and used in its own recursive call

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 29
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 6409
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 16
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 19
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 16473
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 12
//::     end:
//::       line: 6
//::       col: 28
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 18
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'b', which is subject to definite-assignment rules, is always
//::         initialized here
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 7
//::       col: 7
//::     end:
//::       line: 7
//::       col: 20
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 3
//::     end:
//::       line: 8
//::       col: 25
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionManual
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 16214
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 31
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - loop or recursion terminates
//::       - call
//::       - loop or recursion terminates
//::       - call
//::       - loop or recursion terminates
//::       - call
//::       - >-
//::         ensures clause at snapshot_test_assert_cov_complete.dfy(3,11)-(3,19)
//::         from call
//::       - loop or recursion terminates
//::       - call
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - call
//::       - the precondition always holds
//::       - >-
//::         requires clause at snapshot_test_assert_cov_complete.dfy(2,12)-(2,16)
//::         from call
//::       - loop or recursion terminates
//::       - call
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 11097
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 19
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionManual
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 20419
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//:: edges:
//::   provedBy:
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::       provers:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::       provers:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::       provers:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::       provers:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::       provers:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::   proofUnused:
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::       unused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::       unused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::       unused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::       unused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20
//::     - top: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19
//::       unused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::   connections:
//::     - call: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31
//::       targets:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16
//::
