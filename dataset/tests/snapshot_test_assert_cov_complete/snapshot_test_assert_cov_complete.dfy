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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,9|AssertionAutomatic
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 9
//::     prooftext: a value exists that satisfies this let-such-that expression
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 16
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 29
//::     prooftext: a value exists that satisfies this let-such-that expression
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 19
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 6
//::       col: 12
//::     end:
//::       line: 6
//::       col: 28
//::     prooftext: assign-such-that constraint
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 18
//::     prooftext: >-
//::       variable 'b', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 7
//::       col: 7
//::     end:
//::       line: 7
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 3
//::     end:
//::       line: 8
//::       col: 25
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 31
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 19
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,3|AssertionManual
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 8
//::       col: 3
//::     end:
//::       line: 8
//::       col: 3
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,5|AssertionManual
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 5
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,15-3,15|Postcondition
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 3
//::       col: 15
//::     end:
//::       line: 3
//::       col: 15
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|Call
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 31
//::     prooftext: >-
//::       ensures clause at snapshot_test_assert_cov_complete.dfy(3,11)-(3,19) from
//::       call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,24-10,24|AssertionAutomatic
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 10
//::       col: 24
//::     end:
//::       line: 10
//::       col: 24
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,24-10,24|Precondition
//::     file: snapshot_test_assert_cov_complete.dfy
//::     start:
//::       line: 10
//::       col: 24
//::     end:
//::       line: 10
//::       col: 24
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,9|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,3|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,15-3,15|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|Call
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,24-10,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,24-10,24|Precondition
//::       provedBy:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,9-6,29|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|6,12-6,28|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|7,7-7,20|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|8,3-8,25|AssertionManual
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|CodeLine
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|12,5-12,19|AssertionManual
//::   calls:
//::     - id: >-
//::         snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|10,5-10,31|Call
//::       connections:
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|3,11-3,19|Postcondition
//::         - >-
//::           snapshot_test_assert_cov_complete.dfy|CardinalitySubsetLt|correctness|2,12-2,16|Precondition
//::
