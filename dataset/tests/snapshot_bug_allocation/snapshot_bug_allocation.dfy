method append(a:array<int>, b:int) returns (c:array<int>)
  requires a.Length > 0
  ensures a.Length == c.Length
  ensures c[0] == a[0] + 1
{
  //:::  array_append.dfy(12,3)-(12,27): assignment (or return)
  // In Boogie
  //   assume true;
  // assert {:id "id8"} a#0 != null;
  // assume true;
  // assert {:id "id9"} 0 <= _System.array.Length(a#0) + 1;
  // havoc $nw;
  // assume $nw != null && $Is($nw, Tclass._System.array?(TInt));
  // assume !$Unbox(read($Heap, $nw, alloc)): bool;
  // assume _System.array.Length($nw) == _System.array.Length(a#0) + 1;
  // $Heap := update($Heap, $nw, alloc, $Box(true));
  // assume $IsGoodHeap($Heap);
  // assume $IsHeapAnchor($Heap);
  // c#0 := $nw;  (this assigment is not being tranlated as an assume)
  //              (and it is not captured, same problem I figured it out but more internal)
  //              (Unfortunatlye it seems that this has to be handle really on boogie no id call to save us
  // defass#c#0 := true;
  // assume {:captureState "array_append.dfy(10,26)"} true;
  c := new int[a.Length]; 
  c[0] := a[0] + 1;
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|2,14-2,14|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 23
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 11
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 22
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 26
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|3,13-3,13|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|3,25-3,25|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,12-4,12|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|well-formedness|4,20-4,20|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 20
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: well-formedness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|correctness|24,18-24,18|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 18
//::     end:
//::       line: 24
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
//::       snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 16
//::     end:
//::       line: 24
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 26
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 16
//::     end:
//::       line: 24
//::       col: 18
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 3
//::     end:
//::       line: 24
//::       col: 25
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
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
//::       snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 11
//::     end:
//::       line: 25
//::       col: 11
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 11
//::     end:
//::       line: 25
//::       col: 14
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: >-
//::       snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 26
//::       col: 1
//::     end:
//::       line: 26
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
//::       snapshot_bug_allocation.dfy|append|correctness|25,4-25,4|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 4
//::     end:
//::       line: 25
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
//::       snapshot_bug_allocation.dfy|append|correctness|25,12-25,12|AssertionAutomatic
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 12
//::     end:
//::       line: 25
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|3,20-3,20|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 20
//::     end:
//::       line: 3
//::       col: 20
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//::   - id: snapshot_bug_allocation.dfy|append|correctness|4,16-4,16|Postcondition
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 16
//::     end:
//::       line: 4
//::       col: 16
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: append
//::     methodType: correctness
//::     assertionGroup: append
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|well-formedness|2,14-2,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|well-formedness|3,13-3,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|well-formedness|3,25-3,25|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|well-formedness|4,12-4,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|well-formedness|4,20-4,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26|Postcondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|correctness|24,18-24,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::       proofUnused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|correctness|25,4-25,4|AssertionAutomatic
//::       provedBy:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::     - id: >-
//::         snapshot_bug_allocation.dfy|append|correctness|25,12-25,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::       proofUnused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::     - id: snapshot_bug_allocation.dfy|append|correctness|3,20-3,20|Postcondition
//::       provedBy:
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::       proofUnused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::     - id: snapshot_bug_allocation.dfy|append|correctness|4,16-4,16|Postcondition
//::       provedBy:
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26|Postcondition
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19|CodeLine
//::       proofUnused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23|Precondition
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25|Postcondition
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|AssertionAutomatic
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18|CodeLine
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25|CodeLine
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,3|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,3-25,6|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,11|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|25,11-25,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_allocation.dfy|append|correctness|26,1-26,1|AssertionAutomatic
//::   calls: []
//::
