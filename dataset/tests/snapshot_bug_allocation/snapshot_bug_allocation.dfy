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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 14
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 5079
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 13
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 7673
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 23
//::     end:
//::       line: 3
//::       col: 25
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 7788
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 25
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 11
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 7998
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 14
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 8961
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 19
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 8797
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 19
//::     end:
//::       line: 4
//::       col: 22
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 9178
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 26
//::     methodName: append
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 16
//::     end:
//::       line: 24
//::       col: 18
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 5902
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
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
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 25
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 12020
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 26
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 14506
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 24
//::       col: 3
//::     end:
//::       line: 24
//::       col: 25
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
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
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
//::       col: 3
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'c', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 8121
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
//::       col: 6
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 11401
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 11
//::     end:
//::       line: 25
//::       col: 11
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 11278
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 11
//::     end:
//::       line: 25
//::       col: 14
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 11608
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 25
//::       col: 3
//::     end:
//::       line: 25
//::       col: 19
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
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
//::   - locationId: snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     file: snapshot_bug_allocation.dfy
//::     start:
//::       line: 26
//::       col: 1
//::     end:
//::       line: 26
//::       col: 1
//::     methodName: append
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'c', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::     - top: snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::     - top: snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::     - top: snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::       provers:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::   proofUnused:
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,22
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|well-formedness|2,12-2,14
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,13
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,23-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,11
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,19-4,19
//::         - snapshot_bug_allocation.dfy|append|well-formedness|4,11-4,26
//::     - top: snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     - top: snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     - top: snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|2,12-2,23
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::     - top: snapshot_bug_allocation.dfy|append|correctness|25,11-25,14
//::       unused:
//::         - snapshot_bug_allocation.dfy|append|correctness|3,11-3,25
//::         - snapshot_bug_allocation.dfy|append|correctness|4,11-4,26
//::         - snapshot_bug_allocation.dfy|append|correctness|24,16-24,18
//::         - snapshot_bug_allocation.dfy|append|correctness|24,3-24,25
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,3
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,6
//::         - snapshot_bug_allocation.dfy|append|correctness|25,11-25,11
//::         - snapshot_bug_allocation.dfy|append|correctness|25,3-25,19
//::         - snapshot_bug_allocation.dfy|append|correctness|26,1-26,1
//::   connections: []
//::
