method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0 //:: Found unused by proof, Clover_has_close_elements.dfy(4,12)-(4,25): requires clause
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{

  res := false;
  var idx: int := 0;
  var z: int := 0; //:: Redundant Line (artificially added)
  while idx < |numbers| && !res
    invariant 0 <= idx <= |numbers|
    invariant !res //:: Found unused by proof,   Clover_has_close_elements.dfy(13,15)-(13,16): loop invariant
    invariant forall i: int, j: int :: 0 <= i < idx && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold
  {
    var idx2: int := 0;
    while idx2 < idx && !res
      invariant 0 <= idx <= |numbers| //:: Found unused by proof,  Clover_has_close_elements.dfy(18,17)-(18,37): loop invariant
      invariant 0 <= idx2 <= idx
      invariant !res //:: Found unused by proof,  Clover_has_close_elements.dfy(20,17)-(20,18): loop invariant
      invariant forall j: int :: 0 <= j < idx2 ==> (if numbers[idx] - numbers[j] < 0.0 then numbers[j] - numbers[idx] else numbers[idx] - numbers[j]) >= threshold
    {

      var distance :=  (if numbers[idx2] - numbers[idx] < 0.0 then numbers[idx] - numbers[idx2] else numbers[idx2] - numbers[idx]);
      if distance < threshold  {
        res := true;
        return;
      }
      z := z + 1; //::Redundant Line (artificially added)
      idx2 := idx2 + 1;
    }
    idx := idx + 1;
  }
}

// Lurking bug these two lines


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 88
//::     end:
//::       line: 4
//::       col: 97
//::     methodName: has_close_elements
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
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 12505
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 25
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
//::       - method requires clause
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
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 11
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 44
//::     end:
//::       line: 3
//::       col: 61
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 66
//::     end:
//::       line: 3
//::       col: 83
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 88
//::     end:
//::       line: 3
//::       col: 93
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 102
//::     end:
//::       line: 3
//::       col: 111
//::     methodName: has_close_elements
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
//::       batchResourceCount: 9235
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 115
//::     end:
//::       line: 3
//::       col: 124
//::     methodName: has_close_elements
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
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 9399
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 137
//::     end:
//::       line: 3
//::       col: 146
//::     methodName: has_close_elements
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
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 9668
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 150
//::     end:
//::       line: 3
//::       col: 159
//::     methodName: has_close_elements
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
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 9725
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 166
//::     end:
//::       line: 3
//::       col: 175
//::     methodName: has_close_elements
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
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 9627
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 179
//::     end:
//::       line: 3
//::       col: 188
//::     methodName: has_close_elements
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
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 9754
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 98
//::     end:
//::       line: 3
//::       col: 193
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 193
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 12
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 101
//::     end:
//::       line: 4
//::       col: 110
//::     methodName: has_close_elements
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 13056
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 123
//::     end:
//::       line: 4
//::       col: 132
//::     methodName: has_close_elements
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
//::       batchResourceCount: 12983
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 136
//::     end:
//::       line: 4
//::       col: 145
//::     methodName: has_close_elements
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
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 13017
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 152
//::     end:
//::       line: 4
//::       col: 161
//::     methodName: has_close_elements
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
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 12933
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 165
//::     end:
//::       line: 4
//::       col: 174
//::     methodName: has_close_elements
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
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 13060
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 20
//::     end:
//::       line: 4
//::       col: 189
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 189
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 20
//::     methodName: has_close_elements
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
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 15145
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 8
//::       col: 7
//::     end:
//::       line: 8
//::       col: 20
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 25
//::     methodName: has_close_elements
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
//::       isProvedBy: false
//::       isUnused: true
//::     type: Precondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 19
//::     end:
//::       line: 3
//::       col: 193
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 45
//::       batchOutcome: Valid
//::       batchResourceCount: 18688
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 21
//::     end:
//::       line: 4
//::       col: 180
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 46
//::       batchOutcome: Valid
//::       batchResourceCount: 21115
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 7
//::       col: 15
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 9
//::       col: 7
//::     end:
//::       line: 9
//::       col: 18
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 35
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 20
//::     end:
//::       line: 11
//::       col: 35
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 15253
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 12
//::       col: 16
//::     end:
//::       line: 12
//::       col: 16
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 12
//::       col: 15
//::     end:
//::       line: 12
//::       col: 16
//::     methodName: has_close_elements
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
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 15188
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 75
//::     end:
//::       line: 13
//::       col: 84
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 39
//::       batchOutcome: Valid
//::       batchResourceCount: 11241
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 88
//::     end:
//::       line: 13
//::       col: 97
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 40
//::       batchOutcome: Valid
//::       batchResourceCount: 11520
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 110
//::     end:
//::       line: 13
//::       col: 119
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 41
//::       batchOutcome: Valid
//::       batchResourceCount: 11951
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 123
//::     end:
//::       line: 13
//::       col: 132
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 42
//::       batchOutcome: Valid
//::       batchResourceCount: 11395
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 139
//::     end:
//::       line: 13
//::       col: 148
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 43
//::       batchOutcome: Valid
//::       batchResourceCount: 11390
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 152
//::     end:
//::       line: 13
//::       col: 161
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 44
//::       batchOutcome: Valid
//::       batchResourceCount: 11839
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 15
//::     end:
//::       line: 13
//::       col: 167
//::     methodName: has_close_elements
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
//::       batchIndex: 18
//::       batchOutcome: Valid
//::       batchResourceCount: 22726
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 29
//::     end:
//::       line: 10
//::       col: 29
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 15
//::       col: 9
//::     end:
//::       line: 15
//::       col: 23
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 17
//::     end:
//::       line: 17
//::       col: 37
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 17
//::     end:
//::       line: 17
//::       col: 22
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 27
//::       batchOutcome: Valid
//::       batchResourceCount: 16699
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 22
//::     end:
//::       line: 17
//::       col: 37
//::     methodName: has_close_elements
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
//::       batchIndex: 28
//::       batchOutcome: Valid
//::       batchResourceCount: 16741
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 30
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 22
//::     methodName: has_close_elements
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
//::       batchIndex: 29
//::       batchOutcome: Valid
//::       batchResourceCount: 17393
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 22
//::     end:
//::       line: 18
//::       col: 30
//::     methodName: has_close_elements
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
//::       batchIndex: 30
//::       batchOutcome: Valid
//::       batchResourceCount: 17360
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 19
//::       col: 18
//::     end:
//::       line: 19
//::       col: 18
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 19
//::       col: 17
//::     end:
//::       line: 19
//::       col: 18
//::     methodName: has_close_elements
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
//::       batchIndex: 31
//::       batchOutcome: Valid
//::       batchResourceCount: 17235
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 56
//::     end:
//::       line: 20
//::       col: 67
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 33
//::       batchOutcome: Valid
//::       batchResourceCount: 15284
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 71
//::     end:
//::       line: 20
//::       col: 80
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 34
//::       batchOutcome: Valid
//::       batchResourceCount: 16077
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 93
//::     end:
//::       line: 20
//::       col: 102
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 35
//::       batchOutcome: Valid
//::       batchResourceCount: 16985
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 106
//::     end:
//::       line: 20
//::       col: 117
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 36
//::       batchOutcome: Valid
//::       batchResourceCount: 15430
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 124
//::     end:
//::       line: 20
//::       col: 135
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 37
//::       batchOutcome: Valid
//::       batchResourceCount: 15426
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 139
//::     end:
//::       line: 20
//::       col: 148
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 38
//::       batchOutcome: Valid
//::       batchResourceCount: 16970
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 17
//::     end:
//::       line: 20
//::       col: 154
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 32
//::       batchOutcome: Valid
//::       batchResourceCount: 23149
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 26
//::     end:
//::       line: 16
//::       col: 26
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'res', which is subject to definite-assignment rules, is always
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 28
//::     end:
//::       line: 23
//::       col: 40
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 14587
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 44
//::     end:
//::       line: 23
//::       col: 55
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 14712
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 68
//::     end:
//::       line: 23
//::       col: 79
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 21
//::       batchOutcome: Valid
//::       batchResourceCount: 15381
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 83
//::     end:
//::       line: 23
//::       col: 95
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 22
//::       batchOutcome: Valid
//::       batchResourceCount: 15476
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 102
//::     end:
//::       line: 23
//::       col: 114
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 23
//::       batchOutcome: Valid
//::       batchResourceCount: 15365
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 118
//::     end:
//::       line: 23
//::       col: 129
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 24
//::       batchOutcome: Valid
//::       batchResourceCount: 15449
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 131
//::     methodName: has_close_elements
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 25
//::       col: 9
//::     end:
//::       line: 25
//::       col: 20
//::     methodName: has_close_elements
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 26
//::       col: 9
//::     end:
//::       line: 26
//::       col: 15
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
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
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 28
//::       col: 7
//::     end:
//::       line: 28
//::       col: 17
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 29
//::       col: 7
//::     end:
//::       line: 29
//::       col: 23
//::     methodName: has_close_elements
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 18
//::     end:
//::       line: 16
//::       col: 18
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 25
//::       batchOutcome: Valid
//::       batchResourceCount: 16333
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 5
//::     end:
//::       line: 30
//::       col: 5
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 26
//::       batchOutcome: Valid
//::       batchResourceCount: 16614
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 31
//::       col: 5
//::     end:
//::       line: 31
//::       col: 19
//::     methodName: has_close_elements
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
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 23
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 14617
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 32
//::       col: 3
//::     methodName: has_close_elements
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 14860
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 33
//::       col: 1
//::     end:
//::       line: 33
//::       col: 1
//::     methodName: has_close_elements
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'res', which is subject to definite-assignment rules, is
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
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::       provers:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::   proofUnused:
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::     - top: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3
//::       unused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1
//::   connections: []
//::
