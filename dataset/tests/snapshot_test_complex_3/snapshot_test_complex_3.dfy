method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n:= 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant forall i,j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n+1;
    while m != a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m+1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n+1;
  }
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 51
//::     end:
//::       line: 3
//::       col: 51
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,38-3,40|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 38
//::     end:
//::       line: 3
//::       col: 40
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,40|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 40
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,54|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 51
//::     end:
//::       line: 3
//::       col: 54
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,59|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 59
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,62|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 59
//::     end:
//::       line: 3
//::       col: 62
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,62|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 51
//::     end:
//::       line: 3
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,62|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,11-3,62|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,20-4,20|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 20
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 43
//::     end:
//::       line: 4
//::       col: 43
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 43
//::     end:
//::       line: 4
//::       col: 43
//::     prooftext: array is always allocated
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,11-4,49|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 49
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,52-3,52|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 52
//::     end:
//::       line: 3
//::       col: 52
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,60-3,60|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 60
//::     end:
//::       line: 3
//::       col: 60
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,40-3,40|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 40
//::     end:
//::       line: 3
//::       col: 40
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: well-formedness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,17-8,17|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 17
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 6
//::       col: 7
//::     end:
//::       line: 6
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 20
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 62
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 49
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 25
//::     end:
//::       line: 8
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 27
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 20
//::     end:
//::       line: 8
//::       col: 27
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 48
//::     end:
//::       line: 9
//::       col: 50
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 61
//::     end:
//::       line: 9
//::       col: 61
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 61
//::     end:
//::       line: 9
//::       col: 64
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 69
//::     end:
//::       line: 9
//::       col: 69
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 69
//::     end:
//::       line: 9
//::       col: 72
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 15
//::     end:
//::       line: 9
//::       col: 72
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 48
//::     end:
//::       line: 10
//::       col: 48
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 48
//::     end:
//::       line: 10
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 56
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 59
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 24
//::     end:
//::       line: 11
//::       col: 24
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 47
//::     end:
//::       line: 11
//::       col: 47
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 47
//::     end:
//::       line: 11
//::       col: 47
//::     prooftext: array is always allocated
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 53
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 36
//::     end:
//::       line: 15
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 17
//::     end:
//::       line: 15
//::       col: 38
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 17
//::     end:
//::       line: 15
//::       col: 22
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 22
//::     end:
//::       line: 15
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 31
//::     end:
//::       line: 15
//::       col: 38
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 44
//::     end:
//::       line: 16
//::       col: 44
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 44
//::     end:
//::       line: 16
//::       col: 52
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 57
//::     end:
//::       line: 16
//::       col: 57
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 57
//::     end:
//::       line: 16
//::       col: 60
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 17
//::     end:
//::       line: 16
//::       col: 60
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 16
//::     end:
//::       line: 14
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 10
//::     end:
//::       line: 18
//::       col: 10
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 10
//::     end:
//::       line: 18
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 17
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 21
//::       col: 7
//::     end:
//::       line: 21
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 11
//::     end:
//::       line: 14
//::       col: 11
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 22
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 5
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 8
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 11
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 19
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 24
//::     end:
//::       line: 23
//::       col: 24
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 24
//::     end:
//::       line: 23
//::       col: 32
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 39
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 35
//::     end:
//::       line: 23
//::       col: 35
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 35
//::     end:
//::       line: 23
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 19
//::     prooftext: left-hand sides a[mindex] and a[n] are distinct
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 24
//::       col: 5
//::     end:
//::       line: 24
//::       col: 13
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 9
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 25
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,22-8,22|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 22
//::     end:
//::       line: 8
//::       col: 22
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,15|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 15
//::     end:
//::       line: 9
//::       col: 15
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,15|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 15
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|11,31-11,31|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 31
//::     end:
//::       line: 11
//::       col: 31
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|7,16-7,16|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 16
//::     end:
//::       line: 7
//::       col: 16
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,19-15,19|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 19
//::     end:
//::       line: 15
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,29-15,29|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 29
//::     end:
//::       line: 15
//::       col: 29
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,33-15,33|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 33
//::     end:
//::       line: 15
//::       col: 33
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,17|LoopInvariant
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 17
//::     end:
//::       line: 16
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|14,18-14,18|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 18
//::     end:
//::       line: 14
//::       col: 18
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,11-18,11|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 11
//::     end:
//::       line: 18
//::       col: 11
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|18,18-18,18|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 18
//::     end:
//::       line: 18
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-14,5|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 14
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,6-23,6|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 6
//::     end:
//::       line: 23
//::       col: 6
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,12-23,12|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 12
//::     end:
//::       line: 23
//::       col: 12
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,25-23,25|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 25
//::     end:
//::       line: 23
//::       col: 25
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|23,36-23,36|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 36
//::     end:
//::       line: 23
//::       col: 36
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-7,3|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 7
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,45-16,45|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 45
//::     end:
//::       line: 16
//::       col: 45
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|16,58-16,58|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 58
//::     end:
//::       line: 16
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|15,38-15,38|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 38
//::     end:
//::       line: 15
//::       col: 38
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,11|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 11
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|4,27-4,27|Postcondition
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 27
//::     end:
//::       line: 4
//::       col: 27
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,49-10,49|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 49
//::     end:
//::       line: 10
//::       col: 49
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|10,57-10,57|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 57
//::     end:
//::       line: 10
//::       col: 57
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,62-9,62|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 62
//::     end:
//::       line: 9
//::       col: 62
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,70-9,70|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 70
//::     end:
//::       line: 9
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|9,50-9,50|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 50
//::     end:
//::       line: 9
//::       col: 50
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//::   - id: >-
//::       snapshot_test_complex_3.dfy|SelectionSort|correctness|8,27-8,27|AssertionAutomatic
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 27
//::     end:
//::       line: 8
//::       col: 27
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SelectionSort
//::     methodType: correctness
//::     assertionGroup: SelectionSort
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,38-3,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,40|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,20-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,11-4,49|Postcondition
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,52-3,52|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,40|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,54|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,38-3,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,20-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,11-4,49|Postcondition
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,60-3,60|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,40|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,62|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,38-3,40|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,20-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,11-4,49|Postcondition
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,40-3,40|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,38-3,40|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,40|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,59-3,62|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,51-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,25-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,20-4,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,43-4,43|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|well-formedness|4,11-4,49|Postcondition
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|8,17-8,17|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|8,22-8,22|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,15|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,15|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|11,31-11,31|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|7,16-7,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|15,19-15,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|15,29-15,29|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|15,33-15,33|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,17|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|14,18-14,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|18,11-18,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|18,18-18,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-14,5|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|23,6-23,6|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|23,12-23,12|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|23,25-23,25|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|23,36-23,36|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-7,3|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|16,45-16,45|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|16,58-16,58|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|15,38-15,38|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,11|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|4,27-4,27|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|10,49-10,49|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|10,57-10,57|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|9,62-9,62|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|9,70-9,70|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|9,50-9,50|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::     - id: >-
//::         snapshot_test_complex_3.dfy|SelectionSort|correctness|8,27-8,27|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49|Postcondition
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60|LoopInvariant
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13|CodeLine
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9|AssertionAutomatic
//::         - >-
//::           snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3|CodeLine
//::   calls: []
//::
