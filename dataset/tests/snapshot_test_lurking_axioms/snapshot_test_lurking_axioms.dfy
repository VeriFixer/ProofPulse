method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{
  c := new int[a.Length+1];
  var i:= 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall ii::0<= ii <i ==> c[ii]==a[ii] //:: Unused:  _lurking_axioms.dfy(9,15)-(9,49): loop invariant
  {
    c[i] := a[i];
    i:=i+1;
  }
  c[a.Length]:=b;
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|well-formedness|2,12-2,12|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|well-formedness|2,27-2,27|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 2
//::       col: 27
//::     end:
//::       line: 2
//::       col: 27
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|well-formedness|2,12-2,31|Postcondition
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 31
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|4,18-4,18|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 4
//::       col: 18
//::     end:
//::       line: 4
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 4
//::       col: 16
//::     end:
//::       line: 4
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 31
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 4
//::       col: 16
//::     end:
//::       line: 4
//::       col: 25
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 4
//::       col: 3
//::     end:
//::       line: 4
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 5
//::       col: 7
//::     end:
//::       line: 5
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 25
//::     end:
//::       line: 7
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 15
//::     end:
//::       line: 7
//::       col: 27
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 15
//::     end:
//::       line: 7
//::       col: 20
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 20
//::     end:
//::       line: 7
//::       col: 27
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 40
//::     end:
//::       line: 8
//::       col: 40
//::     prooftext: >-
//::       variable 'c', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 40
//::     end:
//::       line: 8
//::       col: 44
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 47
//::     end:
//::       line: 8
//::       col: 47
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 47
//::     end:
//::       line: 8
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 51
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 6
//::       col: 14
//::     end:
//::       line: 6
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 5
//::     prooftext: >-
//::       variable 'c', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 13
//::     end:
//::       line: 10
//::       col: 13
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 13
//::     end:
//::       line: 10
//::       col: 16
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 11
//::       col: 5
//::     end:
//::       line: 11
//::       col: 11
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 6
//::       col: 3
//::     end:
//::       line: 12
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 3
//::     end:
//::       line: 13
//::       col: 3
//::     prooftext: >-
//::       variable 'c', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 5
//::     end:
//::       line: 13
//::       col: 7
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 3
//::     end:
//::       line: 13
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 3
//::     end:
//::       line: 13
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 14
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'c', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|4,24-4,24|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 4
//::       col: 24
//::     end:
//::       line: 4
//::       col: 24
//::     prooftext: array size is never negative
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,17-7,17|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 17
//::     end:
//::       line: 7
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,22-7,22|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 22
//::     end:
//::       line: 7
//::       col: 22
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,15|LoopInvariant
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 15
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|6,16-6,16|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 6
//::       col: 16
//::     end:
//::       line: 6
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,6-10,6|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 6
//::     end:
//::       line: 10
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|10,14-10,14|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 10
//::       col: 14
//::     end:
//::       line: 10
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|6,3-6,3|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 6
//::       col: 3
//::     end:
//::       line: 6
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|13,7-13,7|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 7
//::     end:
//::       line: 13
//::       col: 7
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|13,4-13,4|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 13
//::       col: 4
//::     end:
//::       line: 13
//::       col: 4
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|2,24-2,24|Postcondition
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 2
//::       col: 24
//::     end:
//::       line: 2
//::       col: 24
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,41-8,41|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 41
//::     end:
//::       line: 8
//::       col: 41
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|8,48-8,48|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 8
//::       col: 48
//::     end:
//::       line: 8
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_test_lurking_axioms.dfy|append|correctness|7,27-7,27|AssertionAutomatic
//::     file: snapshot_test_lurking_axioms.dfy
//::     start:
//::       line: 7
//::       col: 27
//::     end:
//::       line: 7
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|well-formedness|2,12-2,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|well-formedness|2,12-2,12|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|well-formedness|2,27-2,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|well-formedness|2,12-2,31|Postcondition
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|4,18-4,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|4,24-4,24|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|7,17-7,17|LoopInvariant
//::       provedBy:
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|7,22-7,22|LoopInvariant
//::       provedBy:
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,15|LoopInvariant
//::       provedBy:
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|6,16-6,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|10,6-10,6|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|10,14-10,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|6,3-6,3|AssertionAutomatic
//::       provedBy:
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|13,7-13,7|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|13,4-13,4|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|2,24-2,24|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|8,41-8,41|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|8,48-8,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_lurking_axioms.dfy|append|correctness|7,27-7,27|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,25-7,27|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|2,12-2,31|Postcondition
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,18|AssertionAutomatic
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,16-4,25|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|4,3-4,27|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|5,7-5,12|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,15-7,20|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|7,20-7,27|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,40-8,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,47-8,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|8,15-8,51|LoopInvariant
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|6,14-6,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,13-10,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|10,5-10,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|11,5-11,11|CodeLine
//::         - snapshot_test_lurking_axioms.dfy|append|correctness|6,3-12,3|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,3|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,5-13,7|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|13,3-13,17|CodeLine
//::         - >-
//::           snapshot_test_lurking_axioms.dfy|append|correctness|14,1-14,1|AssertionAutomatic
//::   calls: []
//::
