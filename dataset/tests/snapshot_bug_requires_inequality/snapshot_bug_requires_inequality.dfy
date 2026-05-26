method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
    requires 0 <= L <= arr.Length
    ensures |firstPart| == L
    ensures |secondPart| == arr.Length - L
    ensures firstPart + secondPart == arr[..]
{
    firstPart := arr[..L];
    secondPart := arr[L..];
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 18
//::     prooftext: array is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 19
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 28
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 42
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 13
//::     end:
//::       line: 5
//::       col: 45
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 25
//::     prooftext: upper bound within range of array
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 5
//::     end:
//::       line: 7
//::       col: 26
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 19
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 26
//::     prooftext: lower bound in range
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 9
//::       col: 1
//::     end:
//::       line: 9
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'firstPart', which is subject to definite-assignment rules,
//::       is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,21-7,21|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 21
//::     end:
//::       line: 7
//::       col: 21
//::     prooftext: upper bound within range of array
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,22-8,22|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 22
//::     end:
//::       line: 8
//::       col: 22
//::     prooftext: lower bound in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,25-3,25|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 3
//::       col: 25
//::     end:
//::       line: 3
//::       col: 25
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,26-4,26|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 26
//::     end:
//::       line: 4
//::       col: 26
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,36-5,36|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 36
//::     end:
//::       line: 5
//::       col: 36
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: correctness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,33-4,33|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 33
//::     end:
//::       line: 4
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 29
//::     end:
//::       line: 4
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 24
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28|Precondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 28
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 42
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 39
//::     end:
//::       line: 5
//::       col: 39
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45|Postcondition
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 13
//::     end:
//::       line: 5
//::       col: 45
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//::   - id: >-
//::       snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,28-2,28|AssertionAutomatic
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 28
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     assertionGroup: SplitArray
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,21-7,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,22-8,22|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,25-3,25|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,26-4,26|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,36-5,36|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26|CodeLine
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,33-4,33|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45|Postcondition
//::     - id: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,28-2,28|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28|Precondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42|Postcondition
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39|AssertionAutomatic
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45|Postcondition
//::   calls: []
//::
