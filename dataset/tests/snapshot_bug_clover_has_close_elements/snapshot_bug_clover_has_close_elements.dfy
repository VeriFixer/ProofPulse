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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,95-4,95|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 95
//::     end:
//::       line: 4
//::       col: 95
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 88
//::     end:
//::       line: 4
//::       col: 97
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 25
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 11
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 44
//::     end:
//::       line: 3
//::       col: 61
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 66
//::     end:
//::       line: 3
//::       col: 83
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 88
//::     end:
//::       line: 3
//::       col: 93
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 102
//::     end:
//::       line: 3
//::       col: 111
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 115
//::     end:
//::       line: 3
//::       col: 124
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 137
//::     end:
//::       line: 3
//::       col: 146
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 150
//::     end:
//::       line: 3
//::       col: 159
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 166
//::     end:
//::       line: 3
//::       col: 175
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 179
//::     end:
//::       line: 3
//::       col: 188
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 98
//::     end:
//::       line: 3
//::       col: 193
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 11
//::     end:
//::       line: 3
//::       col: 193
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 12
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 101
//::     end:
//::       line: 4
//::       col: 110
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 123
//::     end:
//::       line: 4
//::       col: 132
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 136
//::     end:
//::       line: 4
//::       col: 145
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 152
//::     end:
//::       line: 4
//::       col: 161
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 165
//::     end:
//::       line: 4
//::       col: 174
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 20
//::     end:
//::       line: 4
//::       col: 189
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 189
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,108-4,108|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 108
//::     end:
//::       line: 4
//::       col: 108
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,159-4,159|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 159
//::     end:
//::       line: 4
//::       col: 159
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,172-4,172|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 172
//::     end:
//::       line: 4
//::       col: 172
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,130-4,130|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 130
//::     end:
//::       line: 4
//::       col: 130
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,143-4,143|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 143
//::     end:
//::       line: 4
//::       col: 143
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,109-3,109|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 109
//::     end:
//::       line: 3
//::       col: 109
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,122-3,122|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 122
//::     end:
//::       line: 3
//::       col: 122
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,173-3,173|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 173
//::     end:
//::       line: 3
//::       col: 173
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,186-3,186|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 186
//::     end:
//::       line: 3
//::       col: 186
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,144-3,144|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 144
//::     end:
//::       line: 3
//::       col: 144
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,157-3,157|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 157
//::     end:
//::       line: 3
//::       col: 157
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: well-formedness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,17-11,17|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 17
//::     end:
//::       line: 11
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 8
//::       col: 7
//::     end:
//::       line: 8
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 20
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 25
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 19
//::     end:
//::       line: 3
//::       col: 193
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 21
//::     end:
//::       line: 4
//::       col: 180
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 7
//::       col: 3
//::     end:
//::       line: 7
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 9
//::       col: 7
//::     end:
//::       line: 9
//::       col: 18
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 15
//::     end:
//::       line: 11
//::       col: 35
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 20
//::     end:
//::       line: 11
//::       col: 35
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 12
//::       col: 16
//::     end:
//::       line: 12
//::       col: 16
//::     prooftext: >-
//::       variable 'res', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 12
//::       col: 15
//::     end:
//::       line: 12
//::       col: 16
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 75
//::     end:
//::       line: 13
//::       col: 84
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 88
//::     end:
//::       line: 13
//::       col: 97
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 110
//::     end:
//::       line: 13
//::       col: 119
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 123
//::     end:
//::       line: 13
//::       col: 132
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 139
//::     end:
//::       line: 13
//::       col: 148
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 152
//::     end:
//::       line: 13
//::       col: 161
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 15
//::     end:
//::       line: 13
//::       col: 167
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 29
//::     end:
//::       line: 10
//::       col: 29
//::     prooftext: >-
//::       variable 'res', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 15
//::       col: 9
//::     end:
//::       line: 15
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 17
//::     end:
//::       line: 17
//::       col: 37
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 17
//::     end:
//::       line: 17
//::       col: 22
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 22
//::     end:
//::       line: 17
//::       col: 37
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 30
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 17
//::     end:
//::       line: 18
//::       col: 22
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 22
//::     end:
//::       line: 18
//::       col: 30
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 19
//::       col: 18
//::     end:
//::       line: 19
//::       col: 18
//::     prooftext: >-
//::       variable 'res', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 19
//::       col: 17
//::     end:
//::       line: 19
//::       col: 18
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 56
//::     end:
//::       line: 20
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 71
//::     end:
//::       line: 20
//::       col: 80
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 93
//::     end:
//::       line: 20
//::       col: 102
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 106
//::     end:
//::       line: 20
//::       col: 117
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 124
//::     end:
//::       line: 20
//::       col: 135
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 139
//::     end:
//::       line: 20
//::       col: 148
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 17
//::     end:
//::       line: 20
//::       col: 154
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 26
//::     end:
//::       line: 16
//::       col: 26
//::     prooftext: >-
//::       variable 'res', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 28
//::     end:
//::       line: 23
//::       col: 40
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 44
//::     end:
//::       line: 23
//::       col: 55
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 68
//::     end:
//::       line: 23
//::       col: 79
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 83
//::     end:
//::       line: 23
//::       col: 95
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 102
//::     end:
//::       line: 23
//::       col: 114
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 118
//::     end:
//::       line: 23
//::       col: 129
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 11
//::     end:
//::       line: 23
//::       col: 131
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 25
//::       col: 9
//::     end:
//::       line: 25
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 26
//::       col: 9
//::     end:
//::       line: 26
//::       col: 15
//::     prooftext: >-
//::       out-parameter 'res', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 28
//::       col: 7
//::     end:
//::       line: 28
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 29
//::       col: 7
//::     end:
//::       line: 29
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 18
//::     end:
//::       line: 16
//::       col: 18
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 5
//::     end:
//::       line: 30
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 31
//::       col: 5
//::     end:
//::       line: 31
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 23
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 32
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 33
//::       col: 1
//::     end:
//::       line: 33
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'res', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,24-11,24|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 11
//::       col: 24
//::     end:
//::       line: 11
//::       col: 24
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,15|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 12
//::       col: 15
//::     end:
//::       line: 12
//::       col: 15
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,15|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 15
//::     end:
//::       line: 13
//::       col: 15
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,19|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 3
//::       col: 19
//::     end:
//::       line: 3
//::       col: 19
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,21|Postcondition
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 4
//::       col: 21
//::     end:
//::       line: 4
//::       col: 21
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,19-17,19|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 19
//::     end:
//::       line: 17
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,26-17,26|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 17
//::       col: 26
//::     end:
//::       line: 17
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,19-18,19|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 19
//::     end:
//::       line: 18
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,27-18,27|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 18
//::       col: 27
//::     end:
//::       line: 18
//::       col: 27
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,17|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 19
//::       col: 17
//::     end:
//::       line: 19
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,17|LoopInvariant
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 17
//::     end:
//::       line: 20
//::       col: 17
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,15|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 15
//::     end:
//::       line: 10
//::       col: 15
//::     prooftext: decreases expression is bounded below by 0
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-10,3|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 10
//::       col: 3
//::     end:
//::       line: 10
//::       col: 3
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,35-23,35|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 35
//::     end:
//::       line: 23
//::       col: 35
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,51-23,51|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 51
//::     end:
//::       line: 23
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,75-23,75|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 75
//::     end:
//::       line: 23
//::       col: 75
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,90-23,90|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 90
//::     end:
//::       line: 23
//::       col: 90
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,109-23,109|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 109
//::     end:
//::       line: 23
//::       col: 109
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,125-23,125|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 23
//::       col: 125
//::     end:
//::       line: 23
//::       col: 125
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-16,5|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 16
//::       col: 5
//::     end:
//::       line: 16
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,63-20,63|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 63
//::     end:
//::       line: 20
//::       col: 63
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,78-20,78|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 78
//::     end:
//::       line: 20
//::       col: 78
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,100-20,100|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 100
//::     end:
//::       line: 20
//::       col: 100
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,113-20,113|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 113
//::     end:
//::       line: 20
//::       col: 113
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,131-20,131|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 131
//::     end:
//::       line: 20
//::       col: 131
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,146-20,146|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 20
//::       col: 146
//::     end:
//::       line: 20
//::       col: 146
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,82-13,82|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 82
//::     end:
//::       line: 13
//::       col: 82
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,95-13,95|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 95
//::     end:
//::       line: 13
//::       col: 95
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,117-13,117|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 117
//::     end:
//::       line: 13
//::       col: 117
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,130-13,130|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 130
//::     end:
//::       line: 13
//::       col: 130
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,146-13,146|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 146
//::     end:
//::       line: 13
//::       col: 146
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//::   - id: >-
//::       snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,159-13,159|AssertionAutomatic
//::     file: snapshot_bug_clover_has_close_elements.dfy
//::     start:
//::       line: 13
//::       col: 159
//::     end:
//::       line: 13
//::       col: 159
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: has_close_elements
//::     methodType: correctness
//::     assertionGroup: has_close_elements
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,95-4,95|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,108-4,108|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,159-4,159|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,172-4,172|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,130-4,130|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,143-4,143|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,109-3,109|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,122-3,122|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,173-3,173|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,186-3,186|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,144-3,144|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,157-3,157|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,102-3,111|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,150-3,159|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,11|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,44-3,61|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,66-3,83|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,88-3,93|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,115-3,124|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,137-3,146|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,166-3,175|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,179-3,188|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,98-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|3,11-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,12|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,88-4,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,101-4,110|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,123-4,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,136-4,145|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,152-4,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,165-4,174|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,20-4,189|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|well-formedness|4,11-4,189|Postcondition
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,17-11,17|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,24-11,24|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,15|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,15|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,21|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,19-17,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,26-17,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,19-18,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,27-18,27|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,17|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,17|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-10,3|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,35-23,35|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,51-23,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,75-23,75|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,90-23,90|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,109-23,109|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,125-23,125|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-16,5|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,63-20,63|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,78-20,78|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,100-20,100|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,113-20,113|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,131-20,131|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,146-20,146|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,82-13,82|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,95-13,95|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,117-13,117|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,130-13,130|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,146-13,146|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,159-13,159|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,152-13,161|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|2,12-2,25|Precondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|3,19-3,193|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|4,21-4,180|Postcondition
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|7,3-7,15|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|8,7-8,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|9,7-9,18|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,15-11,20|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|11,20-11,35|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,16-12,16|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|12,15-12,16|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,75-13,84|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,88-13,97|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,110-13,119|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,123-13,132|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,139-13,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|13,15-13,167|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,29-10,29|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|15,9-15,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,17-17,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|17,22-17,37|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,17-18,22|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|18,22-18,30|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,18-19,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|19,17-19,18|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,56-20,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,71-20,80|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,93-20,102|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,106-20,117|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,124-20,135|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,139-20,148|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|20,17-20,154|LoopInvariant
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,26-16,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,28-23,40|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,44-23,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,68-23,79|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,83-23,95|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,102-23,114|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,118-23,129|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|23,11-23,131|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|25,9-25,20|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|26,9-26,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|28,7-28,17|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|29,7-29,23|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,18-16,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|16,5-30,5|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|31,5-31,19|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,15-10,23|AssertionAutomatic
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|10,3-32,3|CodeLine
//::         - >-
//::           snapshot_bug_clover_has_close_elements.dfy|has_close_elements|correctness|33,1-33,1|AssertionAutomatic
//::   calls: []
//::
