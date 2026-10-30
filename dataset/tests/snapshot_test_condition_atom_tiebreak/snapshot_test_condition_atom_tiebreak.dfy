method IndexOfMax(a: seq<int>) returns (best: nat)
  requires |a| > 0
  ensures best < |a| && forall j :: 0 <= j < |a| ==> a[j] <= a[best]
{
  best := 0;
  var k := 1;
  while k < |a|
    invariant 1 <= k <= |a| && best < |a|
    invariant forall j :: 0 <= j < k ==> a[j] <= a[best]
  {
    if a[k] > a[best]
       || (a[k] == a[best]
           && k % 2 == 0)
    {
      best := k;
    }
    k := k + 1;
  }
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 5
//::       col: 11
//::     end:
//::       line: 5
//::       col: 11
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 7073
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 18
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Precondition
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 20
//::     methodName: IndexOfMax
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 21
//::       batchOutcome: Valid
//::       batchResourceCount: 10918
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 68
//::     methodName: IndexOfMax
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
//::       - this postcondition holds
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 22
//::       batchOutcome: Valid
//::       batchResourceCount: 12122
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 12
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 6
//::       col: 7
//::     end:
//::       line: 6
//::       col: 13
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 3
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 8
//::       col: 32
//::     end:
//::       line: 8
//::       col: 32
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 26
//::       batchOutcome: Valid
//::       batchResourceCount: 10025
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 41
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 20
//::     methodName: IndexOfMax
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
//::     usedByNumber: 2
//::     topMeta:
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 14406
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 8
//::       col: 20
//::     end:
//::       line: 8
//::       col: 27
//::     methodName: IndexOfMax
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
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 14316
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 8
//::       col: 32
//::     end:
//::       line: 8
//::       col: 41
//::     methodName: IndexOfMax
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
//::     usedByNumber: 3
//::     topMeta:
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 16111
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 9
//::       col: 42
//::     end:
//::       line: 9
//::       col: 45
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 23
//::       batchOutcome: Valid
//::       batchResourceCount: 11324
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 9
//::       col: 52
//::     end:
//::       line: 9
//::       col: 52
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 24
//::       batchOutcome: Valid
//::       batchResourceCount: 11046
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 9
//::       col: 50
//::     end:
//::       line: 9
//::       col: 56
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 25
//::       batchOutcome: Valid
//::       batchResourceCount: 11175
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 9
//::       col: 15
//::     end:
//::       line: 9
//::       col: 56
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 23175
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 15
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 4
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 11
//::       col: 8
//::     end:
//::       line: 11
//::       col: 11
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 11148
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 11
//::       col: 17
//::     end:
//::       line: 11
//::       col: 17
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 10981
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 21
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 11119
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 12
//::       col: 12
//::     end:
//::       line: 12
//::       col: 15
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 11584
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 12
//::       col: 22
//::     end:
//::       line: 12
//::       col: 22
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'best', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 11617
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 12
//::       col: 20
//::     end:
//::       line: 12
//::       col: 26
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 18
//::       batchOutcome: Valid
//::       batchResourceCount: 11739
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 13
//::       col: 15
//::     end:
//::       line: 13
//::       col: 19
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::       - divisor is always non-zero
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 12288
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 15
//::       col: 15
//::     end:
//::       line: 15
//::       col: 15
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::       - value always satisfies the subset constraints of 'nat'
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 14298
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 15
//::       col: 7
//::     end:
//::       line: 15
//::       col: 16
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 11
//::       col: 8
//::     end:
//::       line: 11
//::       col: 21
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 12
//::       col: 12
//::     end:
//::       line: 12
//::       col: 26
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 13
//::       col: 15
//::     end:
//::       line: 13
//::       col: 24
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 17
//::       col: 5
//::     end:
//::       line: 17
//::       col: 15
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 5
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 7
//::       col: 13
//::     end:
//::       line: 7
//::       col: 15
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 13886
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 18
//::       col: 3
//::     methodName: IndexOfMax
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 13915
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     file: snapshot_test_condition_atom_tiebreak.dfy
//::     start:
//::       line: 19
//::       col: 1
//::     end:
//::       line: 19
//::       col: 1
//::     methodName: IndexOfMax
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'best', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 10755
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::       provers:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::   proofUnused:
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::     - top: >-
//::         snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|19,1-19,1
//::       unused:
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|2,12-2,18
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,11-3,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|3,25-3,68
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,11-5,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|5,3-5,12
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|6,7-6,13
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,32
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,15-8,20
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,20-8,27
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|8,32-8,41
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,42-9,45
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,52-9,52
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,50-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|9,15-9,56
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,9-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,11
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,17-11,17
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,15-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,22-12,22
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,20-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,19
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,15-15,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|15,7-15,16
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|11,8-11,21
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|12,12-12,26
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|13,15-13,24
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|17,5-17,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,13-7,15
//::         - >-
//::           snapshot_test_condition_atom_tiebreak.dfy|IndexOfMax|correctness|7,3-18,3
//::   connections: []
//::
