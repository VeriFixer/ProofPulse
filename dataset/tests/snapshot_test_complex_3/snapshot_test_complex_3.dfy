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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 20
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 35
//::       batchOutcome: Valid
//::       batchResourceCount: 29443
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 6
//::       col: 7
//::     end:
//::       line: 6
//::       col: 12
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 62
//::     methodName: SelectionSort
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
//::       - ensures clause
//::       - this postcondition holds
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 48
//::       batchOutcome: Valid
//::       batchResourceCount: 18860
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 49
//::     methodName: SelectionSort
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
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 49
//::       batchOutcome: Valid
//::       batchResourceCount: 17867
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 25
//::     end:
//::       line: 8
//::       col: 27
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchIndex: 65
//::       batchOutcome: Valid
//::       batchResourceCount: 15549
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 27
//::     methodName: SelectionSort
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
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 8
//::       col: 20
//::     end:
//::       line: 8
//::       col: 27
//::     methodName: SelectionSort
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
//::       batchIndex: 36
//::       batchOutcome: Valid
//::       batchResourceCount: 29475
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 48
//::     end:
//::       line: 9
//::       col: 50
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchIndex: 64
//::       batchOutcome: Valid
//::       batchResourceCount: 16753
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 61
//::     end:
//::       line: 9
//::       col: 61
//::     methodName: SelectionSort
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
//::       batchIndex: 60
//::       batchOutcome: Valid
//::       batchResourceCount: 17147
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 61
//::     end:
//::       line: 9
//::       col: 64
//::     methodName: SelectionSort
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
//::       batchIndex: 61
//::       batchOutcome: Valid
//::       batchResourceCount: 17908
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 69
//::     end:
//::       line: 9
//::       col: 69
//::     methodName: SelectionSort
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
//::       batchIndex: 62
//::       batchOutcome: Valid
//::       batchResourceCount: 17247
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 69
//::     end:
//::       line: 9
//::       col: 72
//::     methodName: SelectionSort
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
//::       batchIndex: 63
//::       batchOutcome: Valid
//::       batchResourceCount: 18010
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 9
//::       col: 15
//::     end:
//::       line: 9
//::       col: 72
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
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
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
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
//::       batchIndex: 37
//::       batchOutcome: Valid
//::       batchResourceCount: 61799
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 48
//::     end:
//::       line: 10
//::       col: 48
//::     methodName: SelectionSort
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
//::       batchIndex: 56
//::       batchOutcome: Valid
//::       batchResourceCount: 19286
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 48
//::     end:
//::       line: 10
//::       col: 51
//::     methodName: SelectionSort
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
//::       batchIndex: 57
//::       batchOutcome: Valid
//::       batchResourceCount: 20985
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 56
//::     methodName: SelectionSort
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
//::       batchIndex: 58
//::       batchOutcome: Valid
//::       batchResourceCount: 19380
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 56
//::     end:
//::       line: 10
//::       col: 59
//::     methodName: SelectionSort
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
//::       batchIndex: 59
//::       batchOutcome: Valid
//::       batchResourceCount: 20646
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 59
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
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
//::       - this loop invariant is maintained by the loop
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 38
//::       batchOutcome: Valid
//::       batchResourceCount: 55585
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 24
//::     end:
//::       line: 11
//::       col: 24
//::     methodName: SelectionSort
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
//::       batchIndex: 50
//::       batchOutcome: Valid
//::       batchResourceCount: 20529
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 47
//::     end:
//::       line: 11
//::       col: 47
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is never null
//::       - array is always allocated
//::       - array is always allocated
//::       - array is always allocated
//::       - array is never null
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::       - array is never null
//::       - array is always allocated
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 52
//::       batchOutcome: Valid
//::       batchResourceCount: 20753
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 53
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
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
//::       - this loop invariant is maintained by the loop
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 39
//::       batchOutcome: Valid
//::       batchResourceCount: 78124
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 16
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchIndex: 55
//::       batchOutcome: Valid
//::       batchResourceCount: 21064
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 28
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 36
//::     end:
//::       line: 15
//::       col: 38
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchIndex: 47
//::       batchOutcome: Valid
//::       batchResourceCount: 20051
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 17
//::     end:
//::       line: 15
//::       col: 38
//::     methodName: SelectionSort
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
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 17
//::     end:
//::       line: 15
//::       col: 22
//::     methodName: SelectionSort
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
//::       batchResourceCount: 26727
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 22
//::     end:
//::       line: 15
//::       col: 31
//::     methodName: SelectionSort
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
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 26929
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 15
//::       col: 31
//::     end:
//::       line: 15
//::       col: 38
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
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
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 23978
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 44
//::     end:
//::       line: 16
//::       col: 44
//::     methodName: SelectionSort
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
//::       batchIndex: 43
//::       batchOutcome: Valid
//::       batchResourceCount: 20905
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 44
//::     end:
//::       line: 16
//::       col: 52
//::     methodName: SelectionSort
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
//::       batchIndex: 44
//::       batchOutcome: Valid
//::       batchResourceCount: 22405
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 57
//::     end:
//::       line: 16
//::       col: 57
//::     methodName: SelectionSort
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
//::       batchIndex: 45
//::       batchOutcome: Valid
//::       batchResourceCount: 21003
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 57
//::     end:
//::       line: 16
//::       col: 60
//::     methodName: SelectionSort
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
//::       batchIndex: 46
//::       batchOutcome: Valid
//::       batchResourceCount: 22623
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 16
//::       col: 17
//::     end:
//::       line: 16
//::       col: 60
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
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
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 21
//::       batchOutcome: Valid
//::       batchResourceCount: 47448
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 16
//::     end:
//::       line: 14
//::       col: 18
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchIndex: 42
//::       batchOutcome: Valid
//::       batchResourceCount: 22230
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 10
//::     end:
//::       line: 18
//::       col: 10
//::     methodName: SelectionSort
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
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 20972
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 10
//::     end:
//::       line: 18
//::       col: 13
//::     methodName: SelectionSort
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
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 22020
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 17
//::     methodName: SelectionSort
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
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 21254
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 25
//::     methodName: SelectionSort
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
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 22928
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 20
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 21
//::       col: 7
//::     end:
//::       line: 21
//::       col: 15
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 11
//::     end:
//::       line: 14
//::       col: 11
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 24170
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 14
//::       col: 5
//::     end:
//::       line: 22
//::       col: 5
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 24526
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 5
//::     methodName: SelectionSort
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
//::       batchIndex: 22
//::       batchOutcome: Valid
//::       batchResourceCount: 20786
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 8
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
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
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
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
//::       batchIndex: 24
//::       batchOutcome: Valid
//::       batchResourceCount: 22163
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 11
//::     methodName: SelectionSort
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
//::       batchIndex: 25
//::       batchOutcome: Valid
//::       batchResourceCount: 21283
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 19
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - left-hand sides a[mindex] and a[n] are distinct
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 32
//::       batchOutcome: Valid
//::       batchResourceCount: 22736
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 24
//::     end:
//::       line: 23
//::       col: 24
//::     methodName: SelectionSort
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
//::       batchIndex: 28
//::       batchOutcome: Valid
//::       batchResourceCount: 21746
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 24
//::     end:
//::       line: 23
//::       col: 32
//::     methodName: SelectionSort
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
//::       batchIndex: 29
//::       batchOutcome: Valid
//::       batchResourceCount: 21897
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 39
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 35
//::     end:
//::       line: 23
//::       col: 35
//::     methodName: SelectionSort
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
//::       batchIndex: 30
//::       batchOutcome: Valid
//::       batchResourceCount: 22138
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 23
//::       col: 35
//::     end:
//::       line: 23
//::       col: 38
//::     methodName: SelectionSort
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
//::       batchIndex: 31
//::       batchOutcome: Valid
//::       batchResourceCount: 22270
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 24
//::       col: 5
//::     end:
//::       line: 24
//::       col: 13
//::     methodName: SelectionSort
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
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 9
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 33
//::       batchOutcome: Valid
//::       batchResourceCount: 30800
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     file: snapshot_test_complex_3.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 25
//::       col: 3
//::     methodName: SelectionSort
//::     methodType: correctness
//::     prooftexts:
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 34
//::       batchOutcome: Valid
//::       batchResourceCount: 31655
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::       provers:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::   proofUnused:
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|24,5-24,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::     - top: snapshot_test_complex_3.dfy|SelectionSort|correctness|7,3-25,3
//::       unused:
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|3,11-3,62
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|4,11-4,49
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|6,7-6,12
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,25-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,15-8,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|8,20-8,27
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,48-9,50
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,61
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,61-9,64
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,69
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,69-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|9,15-9,72
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,48
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,48-10,51
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,56
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,56-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|10,15-10,59
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,24-11,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,47-11,47
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|11,15-11,53
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,14-7,16
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|13,9-13,28
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,36-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,17-15,22
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,22-15,31
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|15,31-15,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,44
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,44-16,52
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,57
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,57-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|16,17-16,60
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,16-14,18
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,10
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,10-18,13
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,17
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|18,17-18,25
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|19,9-19,20
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|21,7-21,15
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,11-14,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|14,5-22,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,5
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,8
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,11
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,11-23,19
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,24
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,24-23,32
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,5-23,39
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,35
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|23,35-23,38
//::         - snapshot_test_complex_3.dfy|SelectionSort|correctness|7,9-7,9
//::   connections: []
//::
