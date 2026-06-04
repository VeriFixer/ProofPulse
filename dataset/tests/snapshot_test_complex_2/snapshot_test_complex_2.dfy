// RUN: /compile:0 /nologo

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
    assert A == B';
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
  decreases *
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;

  while count < |P| - 1
    invariant count <= |P| - 1
    invariant count > 0 ==> Special in I
    invariant Special !in S && S < P && S <= I <= P
    invariant if switch then |S| == count + 1 else |S| == count
    decreases *
  { 
    var p :| p in P;
    I := I + {p};

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        switch := true;
      }
    }
  }  

  CardinalitySubsetLt(S, I);

  if I < P {
    CardinalitySubsetLt(I, P);
  }
  assert P <= I;

  assert I == P;
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
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
//::       batchResourceCount: 6473
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
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
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 5
//::       col: 11
//::     end:
//::       line: 5
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
//::       batchResourceCount: 16552
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 8
//::       col: 12
//::     end:
//::       line: 8
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
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 9
//::       col: 18
//::     end:
//::       line: 9
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
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 9
//::       col: 7
//::     end:
//::       line: 9
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
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 10
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
//::       batchResourceCount: 16199
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
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
//::       - ensures clause at snapshot_test_complex_2.dfy(5,11)-(5,19) from call
//::       - loop or recursion terminates
//::       - call
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - call
//::       - the precondition always holds
//::       - requires clause at snapshot_test_complex_2.dfy(4,12)-(4,16) from call
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
//::       batchResourceCount: 11167
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
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
//::       batchResourceCount: 20740
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 29
//::       col: 15
//::     end:
//::       line: 29
//::       col: 30
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 19536
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 19
//::       col: 12
//::     end:
//::       line: 19
//::       col: 18
//::     methodName: strategy
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
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 23
//::       col: 3
//::     end:
//::       line: 23
//::       col: 13
//::     methodName: strategy
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 19
//::       col: 23
//::     end:
//::       line: 19
//::       col: 34
//::     methodName: strategy
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
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
//::       - requires clause
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 20
//::       col: 11
//::     end:
//::       line: 20
//::       col: 26
//::     methodName: strategy
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
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       - ensures clause
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
//::       batchIndex: 24
//::       batchOutcome: Valid
//::       batchResourceCount: 15238
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 24
//::       col: 7
//::     end:
//::       line: 24
//::       col: 14
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 25
//::       col: 7
//::     end:
//::       line: 25
//::       col: 14
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 26
//::       col: 7
//::     end:
//::       line: 26
//::       col: 22
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 29
//::       col: 15
//::     end:
//::       line: 29
//::       col: 15
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 26
//::       batchOutcome: Valid
//::       batchResourceCount: 10024
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 15
//::     end:
//::       line: 30
//::       col: 15
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 27
//::       batchOutcome: Valid
//::       batchResourceCount: 10228
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 15
//::     end:
//::       line: 30
//::       col: 40
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 29
//::     end:
//::       line: 30
//::       col: 40
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 19616
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 15
//::     end:
//::       line: 31
//::       col: 51
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 15
//::     end:
//::       line: 31
//::       col: 27
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 20715
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 32
//::     end:
//::       line: 31
//::       col: 36
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 21862
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 41
//::     end:
//::       line: 31
//::       col: 46
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 22246
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 46
//::     end:
//::       line: 31
//::       col: 51
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 21849
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 37
//::     end:
//::       line: 32
//::       col: 37
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 29
//::       batchOutcome: Valid
//::       batchResourceCount: 11885
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 59
//::     end:
//::       line: 32
//::       col: 59
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 28
//::       batchOutcome: Valid
//::       batchResourceCount: 11881
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 15
//::     end:
//::       line: 32
//::       col: 59
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 30
//::     end:
//::       line: 32
//::       col: 45
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 30496
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 52
//::     end:
//::       line: 32
//::       col: 59
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 18
//::       batchOutcome: Valid
//::       batchResourceCount: 21616
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 9
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 10993
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 35
//::       col: 11
//::     end:
//::       line: 35
//::       col: 20
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
//::       - a value exists that satisfies this let-such-that expression
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
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 12332
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 35
//::       col: 14
//::     end:
//::       line: 35
//::       col: 19
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
//::       - assign-such-that constraint
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 36
//::       col: 15
//::     end:
//::       line: 36
//::       col: 15
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 36
//::       col: 5
//::     end:
//::       line: 36
//::       col: 17
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 38
//::       col: 8
//::     end:
//::       line: 38
//::       col: 8
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 40
//::       col: 9
//::     end:
//::       line: 40
//::       col: 24
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 41
//::       col: 18
//::     end:
//::       line: 41
//::       col: 18
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'count', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 15748
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 41
//::       col: 9
//::     end:
//::       line: 41
//::       col: 27
//::     methodName: strategy
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 44
//::       col: 10
//::     end:
//::       line: 44
//::       col: 10
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 45
//::       col: 19
//::     end:
//::       line: 45
//::       col: 19
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'p', which is subject to definite-assignment rules, is always
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
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 45
//::       col: 9
//::     end:
//::       line: 45
//::       col: 21
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 46
//::       col: 9
//::     end:
//::       line: 46
//::       col: 23
//::     methodName: strategy
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 51
//::       col: 3
//::     end:
//::       line: 51
//::       col: 28
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - the precondition always holds
//::       - requires clause at snapshot_test_complex_2.dfy(4,12)-(4,16) from call
//::       - call
//::       - ensures clause at snapshot_test_complex_2.dfy(5,11)-(5,19) from call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta:
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 12099
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 54
//::       col: 5
//::     end:
//::       line: 54
//::       col: 30
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - ensures clause at snapshot_test_complex_2.dfy(5,11)-(5,19) from call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - the precondition always holds
//::       - requires clause at snapshot_test_complex_2.dfy(4,12)-(4,16) from call
//::       - call
//::       - call
//::       - call
//::       - call
//::       - call
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta:
//::       batchIndex: 25
//::       batchOutcome: Valid
//::       batchResourceCount: 12610
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 56
//::       col: 3
//::     end:
//::       line: 56
//::       col: 16
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
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
//::       batchIndex: 21
//::       batchOutcome: Valid
//::       batchResourceCount: 15825
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 58
//::       col: 3
//::     end:
//::       line: 58
//::       col: 16
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
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
//::       batchIndex: 22
//::       batchOutcome: Valid
//::       batchResourceCount: 16088
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 59
//::       col: 1
//::     end:
//::       line: 59
//::       col: 1
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'count', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 23
//::       batchOutcome: Valid
//::       batchResourceCount: 14045
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 16
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 5
//::       col: 11
//::     end:
//::       line: 5
//::       col: 19
//::     methodName: strategy
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::       provers:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::       provers:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::       provers:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::       provers:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::       provers:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::       provers:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::   proofUnused:
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::       unused:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::       unused:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::       unused:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::       unused:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20
//::     - top: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19
//::       unused:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::     - top: snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1
//::       unused:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34
//::         - snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46
//::         - snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45
//::         - snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59
//::         - snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17
//::         - snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27
//::         - snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::         - snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16
//::   connections:
//::     - call: snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31
//::       targets:
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16
//::     - call: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28
//::       targets:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16
//::         - snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19
//::     - call: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30
//::       targets:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19
//::         - snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16
//::
