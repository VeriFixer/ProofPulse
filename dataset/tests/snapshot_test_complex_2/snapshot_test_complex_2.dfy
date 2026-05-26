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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,9|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 5
//::       col: 11
//::     end:
//::       line: 5
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 8
//::       col: 12
//::     end:
//::       line: 8
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 9
//::       col: 18
//::     end:
//::       line: 9
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 9
//::       col: 7
//::     end:
//::       line: 9
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 10
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,3|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 10
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,5|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,15-5,15|Postcondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 5
//::       col: 15
//::     end:
//::       line: 5
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|Call
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 31
//::     prooftext: ensures clause at snapshot_test_complex_2.dfy(5,11)-(5,19) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: >-
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,24-12,24|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 12
//::       col: 24
//::     end:
//::       line: 12
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
//::       snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,24-12,24|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 12
//::       col: 24
//::     end:
//::       line: 12
//::       col: 24
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: CardinalitySubsetLt
//::     methodType: correctness
//::     assertionGroup: CardinalitySubsetLt
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|29,21-29,21|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 29
//::       col: 21
//::     end:
//::       line: 29
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 19
//::       col: 12
//::     end:
//::       line: 19
//::       col: 18
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 23
//::       col: 3
//::     end:
//::       line: 23
//::       col: 13
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 29
//::       col: 15
//::     end:
//::       line: 29
//::       col: 30
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 19
//::       col: 23
//::     end:
//::       line: 19
//::       col: 34
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 20
//::       col: 11
//::     end:
//::       line: 20
//::       col: 26
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 24
//::       col: 7
//::     end:
//::       line: 24
//::       col: 14
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 25
//::       col: 7
//::     end:
//::       line: 25
//::       col: 14
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 26
//::       col: 7
//::     end:
//::       line: 26
//::       col: 22
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 29
//::       col: 15
//::     end:
//::       line: 29
//::       col: 15
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 15
//::     end:
//::       line: 30
//::       col: 15
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 15
//::     end:
//::       line: 30
//::       col: 40
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 29
//::     end:
//::       line: 30
//::       col: 40
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 15
//::     end:
//::       line: 31
//::       col: 51
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 15
//::     end:
//::       line: 31
//::       col: 27
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 32
//::     end:
//::       line: 31
//::       col: 36
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 41
//::     end:
//::       line: 31
//::       col: 46
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 46
//::     end:
//::       line: 31
//::       col: 51
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 37
//::     end:
//::       line: 32
//::       col: 37
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 59
//::     end:
//::       line: 32
//::       col: 59
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 15
//::     end:
//::       line: 32
//::       col: 59
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 30
//::     end:
//::       line: 32
//::       col: 45
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 52
//::     end:
//::       line: 32
//::       col: 59
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 28
//::       col: 9
//::     end:
//::       line: 28
//::       col: 9
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 35
//::       col: 11
//::     end:
//::       line: 35
//::       col: 20
//::     prooftext: a value exists that satisfies this let-such-that expression
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 35
//::       col: 14
//::     end:
//::       line: 35
//::       col: 19
//::     prooftext: assign-such-that constraint
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 36
//::       col: 15
//::     end:
//::       line: 36
//::       col: 15
//::     prooftext: >-
//::       variable 'p', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 36
//::       col: 5
//::     end:
//::       line: 36
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 38
//::       col: 8
//::     end:
//::       line: 38
//::       col: 8
//::     prooftext: >-
//::       variable 'p', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 40
//::       col: 9
//::     end:
//::       line: 40
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 41
//::       col: 18
//::     end:
//::       line: 41
//::       col: 18
//::     prooftext: >-
//::       variable 'count', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 41
//::       col: 9
//::     end:
//::       line: 41
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 44
//::       col: 10
//::     end:
//::       line: 44
//::       col: 10
//::     prooftext: >-
//::       variable 'p', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 45
//::       col: 19
//::     end:
//::       line: 45
//::       col: 19
//::     prooftext: >-
//::       variable 'p', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 45
//::       col: 9
//::     end:
//::       line: 45
//::       col: 21
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 46
//::       col: 9
//::     end:
//::       line: 46
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 51
//::       col: 3
//::     end:
//::       line: 51
//::       col: 28
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 54
//::       col: 5
//::     end:
//::       line: 54
//::       col: 30
//::     prooftext: call
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 56
//::       col: 3
//::     end:
//::       line: 56
//::       col: 16
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 58
//::       col: 3
//::     end:
//::       line: 58
//::       col: 16
//::     prooftext: assertion always holds
//::     isTopAssertion: false
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 59
//::       col: 1
//::     end:
//::       line: 59
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'count', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|30,37-30,37|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 30
//::       col: 37
//::     end:
//::       line: 30
//::       col: 37
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,23-31,23|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 23
//::     end:
//::       line: 31
//::       col: 23
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,34-31,34|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 34
//::     end:
//::       line: 31
//::       col: 34
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,43-31,43|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 43
//::     end:
//::       line: 31
//::       col: 43
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|31,48-31,48|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 31
//::       col: 48
//::     end:
//::       line: 31
//::       col: 48
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|32,34-32,34|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 34
//::     end:
//::       line: 32
//::       col: 34
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|32,56-32,56|LoopInvariant
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 32
//::       col: 56
//::     end:
//::       line: 32
//::       col: 56
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: >-
//::       snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,11|AssertionAutomatic
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 35
//::       col: 11
//::     end:
//::       line: 35
//::       col: 11
//::     prooftext: a value exists that satisfies this let-such-that expression
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|51,22-51,22|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 51
//::       col: 22
//::     end:
//::       line: 51
//::       col: 22
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|Call
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 51
//::       col: 3
//::     end:
//::       line: 51
//::       col: 28
//::     prooftext: requires clause at snapshot_test_complex_2.dfy(4,12)-(4,16) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 4
//::       col: 12
//::     end:
//::       line: 4
//::       col: 16
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,3|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 56
//::       col: 3
//::     end:
//::       line: 56
//::       col: 3
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19|Postcondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 5
//::       col: 11
//::     end:
//::       line: 5
//::       col: 19
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|Call
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 54
//::       col: 5
//::     end:
//::       line: 54
//::       col: 30
//::     prooftext: ensures clause at snapshot_test_complex_2.dfy(5,11)-(5,19) from call
//::     isTopAssertion: false
//::     type: Call
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,3|AssertionManual
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 58
//::       col: 3
//::     end:
//::       line: 58
//::       col: 3
//::     prooftext: assertion always holds
//::     isTopAssertion: true
//::     type: AssertionManual
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|20,17-20,17|Postcondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 20
//::       col: 17
//::     end:
//::       line: 20
//::       col: 17
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//::   - id: snapshot_test_complex_2.dfy|strategy|correctness|54,24-54,24|Precondition
//::     file: snapshot_test_complex_2.dfy
//::     start:
//::       line: 54
//::       col: 24
//::     end:
//::       line: 54
//::       col: 24
//::     prooftext: the precondition always holds
//::     isTopAssertion: true
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: strategy
//::     methodType: correctness
//::     assertionGroup: strategy
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,9|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,3|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,5|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,15-5,15|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|Call
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,24-12,24|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,24-12,24|Precondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,9-8,29|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|8,12-8,28|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,18-9,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|9,7-9,20|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|10,3-10,25|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|14,5-14,19|AssertionManual
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|29,21-29,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|30,37-30,37|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|31,23-31,23|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|31,34-31,34|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|31,43-31,43|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|31,48-31,48|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|32,34-32,34|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|32,56-32,56|LoopInvariant
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|51,22-51,22|Precondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,3|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|Call
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|Call
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,3|AssertionManual
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|20,17-20,17|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_2.dfy|strategy|correctness|54,24-54,24|Precondition
//::       provedBy:
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|Call
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,12-19,18|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|19,23-19,34|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|20,11-20,26|Postcondition
//::         - snapshot_test_complex_2.dfy|strategy|correctness|23,3-23,13|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|24,7-24,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|25,7-25,14|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|26,7-26,22|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|29,15-29,30|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,15-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|30,29-30,40|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,15-31,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,32-31,36|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,41-31,46|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|31,46-31,51|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,37-32,37|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,59-32,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,15-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,30-32,45|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|32,52-32,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|28,9-28,9|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,11-35,20|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|35,14-35,19|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|36,15-36,15|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|36,5-36,17|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|38,8-38,8|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|40,9-40,24|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|41,18-41,18|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|41,9-41,27|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|44,10-44,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|45,19-45,19|AssertionAutomatic
//::         - snapshot_test_complex_2.dfy|strategy|correctness|45,9-45,21|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|46,9-46,23|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|CodeLine
//::         - snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|CodeLine
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|56,3-56,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|58,3-58,16|AssertionManual
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|59,1-59,1|AssertionAutomatic
//::   calls:
//::     - id: >-
//::         snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|12,5-12,31|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|CardinalitySubsetLt|correctness|4,12-4,16|Precondition
//::     - id: snapshot_test_complex_2.dfy|strategy|correctness|51,3-51,28|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16|Precondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19|Postcondition
//::     - id: snapshot_test_complex_2.dfy|strategy|correctness|54,5-54,30|Call
//::       connections:
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|5,11-5,19|Postcondition
//::         - >-
//::           snapshot_test_complex_2.dfy|strategy|correctness|4,12-4,16|Precondition
//::
