method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    for i := 0 to |s|
        // invariant 0 <= i <= |s| // this is not needed on a for
        invariant |v| == i
        invariant forall k :: 0 <= k < i ==> v[k] == s[k]
    {
        v := v + [s[i]];
    }
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 6
//::       col: 14
//::     end:
//::       line: 6
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 6
//::       col: 14
//::     end:
//::       line: 6
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 53
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 12
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 8
//::       col: 20
//::     end:
//::       line: 8
//::       col: 20
//::     prooftext: >-
//::       variable 'v', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 26
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 46
//::     end:
//::       line: 9
//::       col: 46
//::     prooftext: >-
//::       variable 'v', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 46
//::     end:
//::       line: 9
//::       col: 49
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 54
//::     end:
//::       line: 9
//::       col: 57
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 57
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 11
//::       col: 14
//::     end:
//::       line: 11
//::       col: 14
//::     prooftext: >-
//::       variable 'v', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 22
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 11
//::       col: 9
//::     end:
//::       line: 11
//::       col: 24
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 13
//::       col: 1
//::     end:
//::       line: 13
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'v', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,23-8,23|LoopInvariant
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 8
//::       col: 23
//::     end:
//::       line: 8
//::       col: 23
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,19|LoopInvariant
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,20-11,20|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 11
//::       col: 20
//::     end:
//::       line: 11
//::       col: 20
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,17-2,17|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 2
//::       col: 17
//::     end:
//::       line: 2
//::       col: 17
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,13|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,47-9,47|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 47
//::     end:
//::       line: 9
//::       col: 47
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,55-9,55|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 9
//::       col: 55
//::     end:
//::       line: 9
//::       col: 55
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: correctness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,43-3,43|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 43
//::     end:
//::       line: 3
//::       col: 43
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|2,13-2,22|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 22
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,36|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 36
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,45|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 42
//::     end:
//::       line: 3
//::       col: 45
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,50-3,53|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,53|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 42
//::     end:
//::       line: 3
//::       col: 53
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,53|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 53
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,13-3,53|Postcondition
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 53
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//::   - id: >-
//::       snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,51-3,51|AssertionAutomatic
//::     file: snapshot_test_forall_needs_merging.dfy
//::     start:
//::       line: 3
//::       col: 51
//::     end:
//::       line: 3
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitStringIntoChars
//::     methodType: well-formedness
//::     assertionGroup: SplitStringIntoChars
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,23-8,23|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,20-11,20|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,17-2,17|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,47-9,47|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,55-9,55|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,54-9,57|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|3,13-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|5,5-5,12|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|6,14-6,14|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,20-8,20|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|8,19-8,26|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,46|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,46-9,49|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|9,19-9,57|LoopInvariant
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,14-11,14|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,19-11,22|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|11,9-11,24|CodeLine
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|correctness|13,1-13,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,43-3,43|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,36|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,45|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,50-3,53|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,13-3,53|Postcondition
//::     - id: >-
//::         snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,51-3,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,36|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,45|AssertionAutomatic
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,50-3,53|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,42-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,25-3,53|Postcondition
//::         - >-
//::           snapshot_test_forall_needs_merging.dfy|SplitStringIntoChars|well-formedness|3,13-3,53|Postcondition
//::   calls: []
//::
