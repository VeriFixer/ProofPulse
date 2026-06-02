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
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 18
//::     methodName: SplitArray
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 9375
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 19
//::     methodName: SplitArray
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 19
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: SplitArray
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 28
//::     methodName: SplitArray
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 15885
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 42
//::     methodName: SplitArray
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 16487
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 13
//::     end:
//::       line: 5
//::       col: 45
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 20668
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 18
//::     end:
//::       line: 7
//::       col: 25
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::       - upper bound within range of array
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 9620
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 7
//::       col: 5
//::     end:
//::       line: 7
//::       col: 26
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 19
//::     methodName: SplitArray
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 13331
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 26
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::       - lower bound in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 13425
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 27
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 9
//::       col: 1
//::     end:
//::       line: 9
//::       col: 1
//::     methodName: SplitArray
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'firstPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::       - >-
//::         out-parameter 'secondPart', which is subject to definite-assignment
//::         rules, is always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 29
//::     end:
//::       line: 4
//::       col: 33
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchResourceCount: 12163
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 24
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchResourceCount: 8687
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 28
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 4
//::       col: 13
//::     end:
//::       line: 4
//::       col: 42
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 39
//::     end:
//::       line: 5
//::       col: 39
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 12445
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45
//::     file: snapshot_bug_requires_inequality.dfy
//::     start:
//::       line: 5
//::       col: 13
//::     end:
//::       line: 5
//::       col: 45
//::     methodName: SplitArray
//::     methodType: well-formedness
//::     prooftexts:
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
//:: edges:
//::   provedBy:
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::       provers:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::       provers:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::       provers:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::       provers:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::       provers:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::   proofUnused:
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,19-2,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,25
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,26
//::       unused:
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|2,14-2,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|3,13-3,28
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|4,13-4,42
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|5,13-5,45
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,18-7,18
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|7,5-7,26
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,19-8,19
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|8,5-8,27
//::         - snapshot_bug_requires_inequality.dfy|SplitArray|correctness|9,1-9,1
//::     - top: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33
//::       unused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45
//::     - top: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28
//::       unused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45
//::     - top: >-
//::         snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,39-5,39
//::       unused:
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,24-2,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|2,14-2,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|3,13-3,28
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,29-4,33
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|4,13-4,42
//::         - >-
//::           snapshot_bug_requires_inequality.dfy|SplitArray|well-formedness|5,13-5,45
//::   connections: []
//::
