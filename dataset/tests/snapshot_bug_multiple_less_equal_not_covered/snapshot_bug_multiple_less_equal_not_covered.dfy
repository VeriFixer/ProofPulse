method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
  requires s.Length > 0
  requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
  ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{
    var minSecondIndex := 0;
    for i := 1 to s.Length
        invariant 0 <= i <= s.Length
        invariant 0 <= minSecondIndex < i
        invariant forall j :: 0 <= j < i ==> s[minSecondIndex][1] <= s[j][1]
    {
        if s[i][1] < s[minSecondIndex][1]
        {
            minSecondIndex := i;
        }
    }
    firstOfMinSecond := s[minSecondIndex][0];
}

// but if chained is reparted into two it works:

method MinSecondValueFirst1(s: array<seq<int>>) returns (firstOfMinSecond: int)
  requires s.Length > 0
  requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
  ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{
    var minSecondIndex := 0;
    for i := 1 to s.Length
        invariant 0 <= i
        invariant i <= s.Length
        invariant 0 <= minSecondIndex < i
        invariant forall j :: 0 <= j < i ==> s[minSecondIndex][1] <= s[j][1]
    {
        if s[i][1] < s[minSecondIndex][1]
        {
            minSecondIndex := i;
        }
    }
    firstOfMinSecond := s[minSecondIndex][0];
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,14-2,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 33
//::     end:
//::       line: 3
//::       col: 35
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 35
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 47
//::     end:
//::       line: 3
//::       col: 47
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 47
//::     end:
//::       line: 3
//::       col: 50
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 46
//::     end:
//::       line: 3
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 12
//::     end:
//::       line: 3
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 32
//::     end:
//::       line: 4
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 23
//::     end:
//::       line: 4
//::       col: 34
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 64
//::     end:
//::       line: 4
//::       col: 64
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 64
//::     end:
//::       line: 4
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 64
//::     end:
//::       line: 4
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 44
//::     end:
//::       line: 4
//::       col: 70
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 31
//::     end:
//::       line: 5
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 44
//::     end:
//::       line: 5
//::       col: 44
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 44
//::     end:
//::       line: 5
//::       col: 47
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 44
//::     end:
//::       line: 5
//::       col: 50
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 55
//::     end:
//::       line: 5
//::       col: 55
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 55
//::     end:
//::       line: 5
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 55
//::     end:
//::       line: 5
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,48-3,48|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 48
//::     end:
//::       line: 3
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,65-4,65|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 65
//::     end:
//::       line: 4
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,68-4,68|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 68
//::     end:
//::       line: 4
//::       col: 68
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,45-5,45|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 45
//::     end:
//::       line: 5
//::       col: 45
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,48-5,48|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 48
//::     end:
//::       line: 5
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,56-5,56|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 56
//::     end:
//::       line: 5
//::       col: 56
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,59-5,59|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 59
//::     end:
//::       line: 5
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,33-5,33|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 5
//::       col: 33
//::     end:
//::       line: 5
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,34-4,34|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 34
//::     end:
//::       line: 4
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,35-3,35|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 35
//::     end:
//::       line: 3
//::       col: 35
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,21-8,21|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 8
//::       col: 21
//::     end:
//::       line: 8
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 2
//::       col: 12
//::     end:
//::       line: 2
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 3
//::       col: 12
//::     end:
//::       line: 3
//::       col: 56
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 5
//::       col: 62
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 8
//::       col: 14
//::     end:
//::       line: 8
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 29
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 24
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 41
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 10
//::       col: 24
//::     end:
//::       line: 10
//::       col: 41
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 46
//::     end:
//::       line: 11
//::       col: 46
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 46
//::     end:
//::       line: 11
//::       col: 62
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 46
//::     end:
//::       line: 11
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 70
//::     end:
//::       line: 11
//::       col: 70
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 70
//::     end:
//::       line: 11
//::       col: 73
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 70
//::     end:
//::       line: 11
//::       col: 76
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 76
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 12
//::     end:
//::       line: 13
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 12
//::     end:
//::       line: 13
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 12
//::     end:
//::       line: 13
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 22
//::     end:
//::       line: 13
//::       col: 22
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 22
//::     end:
//::       line: 13
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 22
//::     end:
//::       line: 13
//::       col: 41
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 15
//::       col: 13
//::     end:
//::       line: 15
//::       col: 32
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 25
//::     end:
//::       line: 18
//::       col: 25
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 25
//::     end:
//::       line: 18
//::       col: 41
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 25
//::     end:
//::       line: 18
//::       col: 44
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 5
//::     end:
//::       line: 18
//::       col: 45
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 19
//::       col: 1
//::     end:
//::       line: 19
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'firstOfMinSecond', which is subject to definite-assignment
//::       rules, is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 8
//::       col: 14
//::     end:
//::       line: 8
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,21-9,21|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 21
//::     end:
//::       line: 9
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,26-9,26|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 26
//::     end:
//::       line: 9
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,21-10,21|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 10
//::       col: 21
//::     end:
//::       line: 10
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,39-10,39|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 10
//::       col: 39
//::     end:
//::       line: 10
//::       col: 39
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,19|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,13-13,13|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 13
//::     end:
//::       line: 13
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,16-13,16|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 16
//::     end:
//::       line: 13
//::       col: 16
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,23-13,23|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 23
//::     end:
//::       line: 13
//::       col: 23
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,39-13,39|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 13
//::       col: 39
//::     end:
//::       line: 13
//::       col: 39
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,26-18,26|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 26
//::     end:
//::       line: 18
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,42-18,42|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 18
//::       col: 42
//::     end:
//::       line: 18
//::       col: 42
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-4,11|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 4
//::       col: 11
//::     end:
//::       line: 4
//::       col: 11
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,47-11,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 47
//::     end:
//::       line: 11
//::       col: 47
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,63-11,63|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 63
//::     end:
//::       line: 11
//::       col: 63
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,71-11,71|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 71
//::     end:
//::       line: 11
//::       col: 71
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,74-11,74|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 11
//::       col: 74
//::     end:
//::       line: 11
//::       col: 74
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,31-9,31|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 9
//::       col: 31
//::     end:
//::       line: 9
//::       col: 31
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,14-24,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 24
//::       col: 14
//::     end:
//::       line: 24
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 24
//::       col: 12
//::     end:
//::       line: 24
//::       col: 14
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 24
//::       col: 12
//::     end:
//::       line: 24
//::       col: 23
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 33
//::     end:
//::       line: 25
//::       col: 35
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 24
//::     end:
//::       line: 25
//::       col: 35
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 47
//::     end:
//::       line: 25
//::       col: 47
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 47
//::     end:
//::       line: 25
//::       col: 50
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 46
//::     end:
//::       line: 25
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 24
//::     end:
//::       line: 25
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 12
//::     end:
//::       line: 25
//::       col: 56
//::     prooftext: method requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 32
//::     end:
//::       line: 26
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 23
//::     end:
//::       line: 26
//::       col: 34
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 64
//::     end:
//::       line: 26
//::       col: 64
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 64
//::     end:
//::       line: 26
//::       col: 67
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 64
//::     end:
//::       line: 26
//::       col: 70
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 44
//::     end:
//::       line: 26
//::       col: 70
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 31
//::     end:
//::       line: 27
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 44
//::     end:
//::       line: 27
//::       col: 44
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 44
//::     end:
//::       line: 27
//::       col: 47
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 44
//::     end:
//::       line: 27
//::       col: 50
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 55
//::     end:
//::       line: 27
//::       col: 55
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 55
//::     end:
//::       line: 27
//::       col: 58
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 55
//::     end:
//::       line: 27
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 9
//::     end:
//::       line: 27
//::       col: 62
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,48-25,48|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 48
//::     end:
//::       line: 25
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,65-26,65|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 65
//::     end:
//::       line: 26
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,68-26,68|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 68
//::     end:
//::       line: 26
//::       col: 68
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,45-27,45|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 45
//::     end:
//::       line: 27
//::       col: 45
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,48-27,48|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 48
//::     end:
//::       line: 27
//::       col: 48
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,56-27,56|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 56
//::     end:
//::       line: 27
//::       col: 56
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,59-27,59|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 59
//::     end:
//::       line: 27
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,33-27,33|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 27
//::       col: 33
//::     end:
//::       line: 27
//::       col: 33
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,34-26,34|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 34
//::     end:
//::       line: 26
//::       col: 34
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,35-25,35|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 35
//::     end:
//::       line: 25
//::       col: 35
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: well-formedness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,21-30,21|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 30
//::       col: 21
//::     end:
//::       line: 30
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 30
//::       col: 19
//::     end:
//::       line: 30
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 24
//::       col: 12
//::     end:
//::       line: 24
//::       col: 23
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 25
//::       col: 12
//::     end:
//::       line: 25
//::       col: 56
//::     prooftext: requires clause
//::     isTopAssertion: false
//::     type: Precondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 11
//::     end:
//::       line: 27
//::       col: 62
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 29
//::       col: 9
//::     end:
//::       line: 29
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 30
//::       col: 14
//::     end:
//::       line: 30
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 31
//::       col: 19
//::     end:
//::       line: 31
//::       col: 24
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 32
//::       col: 24
//::     end:
//::       line: 32
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 32
//::       col: 19
//::     end:
//::       line: 32
//::       col: 26
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 33
//::       col: 19
//::     end:
//::       line: 33
//::       col: 41
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 33
//::       col: 19
//::     end:
//::       line: 33
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 33
//::       col: 24
//::     end:
//::       line: 33
//::       col: 41
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 46
//::     end:
//::       line: 34
//::       col: 46
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 46
//::     end:
//::       line: 34
//::       col: 62
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 46
//::     end:
//::       line: 34
//::       col: 65
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 70
//::     end:
//::       line: 34
//::       col: 70
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 70
//::     end:
//::       line: 34
//::       col: 73
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 70
//::     end:
//::       line: 34
//::       col: 76
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 19
//::     end:
//::       line: 34
//::       col: 76
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 12
//::     end:
//::       line: 36
//::       col: 12
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 12
//::     end:
//::       line: 36
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 12
//::     end:
//::       line: 36
//::       col: 18
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 22
//::     end:
//::       line: 36
//::       col: 22
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 22
//::     end:
//::       line: 36
//::       col: 38
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 22
//::     end:
//::       line: 36
//::       col: 41
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 38
//::       col: 13
//::     end:
//::       line: 38
//::       col: 32
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 25
//::     end:
//::       line: 41
//::       col: 25
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 25
//::     end:
//::       line: 41
//::       col: 41
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 25
//::     end:
//::       line: 41
//::       col: 44
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 5
//::     end:
//::       line: 41
//::       col: 45
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 42
//::       col: 1
//::     end:
//::       line: 42
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'firstOfMinSecond', which is subject to definite-assignment
//::       rules, is always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 30
//::       col: 14
//::     end:
//::       line: 30
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,21-31,21|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 31
//::       col: 21
//::     end:
//::       line: 31
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,21-32,21|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 32
//::       col: 21
//::     end:
//::       line: 32
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,21-33,21|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 33
//::       col: 21
//::     end:
//::       line: 33
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,39-33,39|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 33
//::       col: 39
//::     end:
//::       line: 33
//::       col: 39
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,19|LoopInvariant
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 19
//::     end:
//::       line: 34
//::       col: 19
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,13-36,13|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 13
//::     end:
//::       line: 36
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,16-36,16|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 16
//::     end:
//::       line: 36
//::       col: 16
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,23-36,23|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 23
//::     end:
//::       line: 36
//::       col: 23
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,39-36,39|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 36
//::       col: 39
//::     end:
//::       line: 36
//::       col: 39
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,26-41,26|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 26
//::     end:
//::       line: 41
//::       col: 26
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,42-41,42|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 41
//::       col: 42
//::     end:
//::       line: 41
//::       col: 42
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-26,11|Postcondition
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 26
//::       col: 11
//::     end:
//::       line: 26
//::       col: 11
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,26-32,26|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 32
//::       col: 26
//::     end:
//::       line: 32
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,47-34,47|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 47
//::     end:
//::       line: 34
//::       col: 47
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,63-34,63|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 63
//::     end:
//::       line: 34
//::       col: 63
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,71-34,71|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 71
//::     end:
//::       line: 34
//::       col: 71
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//::   - id: >-
//::       snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,74-34,74|AssertionAutomatic
//::     file: snapshot_bug_multiple_less_equal_not_covered.dfy
//::     start:
//::       line: 34
//::       col: 74
//::     end:
//::       line: 34
//::       col: 74
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: MinSecondValueFirst1
//::     methodType: correctness
//::     assertionGroup: MinSecondValueFirst1
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,14-2,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,48-3,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,65-4,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,68-4,68|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,45-5,45|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,48-5,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,56-5,56|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,59-5,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,33-5,33|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,34-4,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,35-3,35|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,33-3,35|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,47-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,46-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,24-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,32-4,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,23-4,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,64-4,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|4,44-4,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,31-5,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,44-5,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,55-5,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|well-formedness|5,9-5,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,21-8,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,21-9,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,26-9,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,21-10,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,39-10,39|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,13-13,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,16-13,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,23-13,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,39-13,39|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,26-18,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,42-18,42|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-4,11|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,47-11,47|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,63-11,63|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,71-11,71|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,74-11,74|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,31-9,31|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,29-9,31|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|2,12-2,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|3,12-3,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|4,11-5,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|7,9-7,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,19-8,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|8,14-8,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|9,24-9,31|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,19-10,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|10,24-10,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,46-11,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,70-11,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|11,19-11,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,12-13,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|13,22-13,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|15,13-15,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,25-18,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|18,5-18,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst|correctness|19,1-19,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,14-24,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,48-25,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,65-26,65|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,68-26,68|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,45-27,45|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,48-27,48|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,56-27,56|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,59-27,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,33-27,33|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,34-26,34|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,35-25,35|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,33-25,35|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,14|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,35|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,47-25,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,46-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,24-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,32-26,34|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,23-26,34|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,64|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,67|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,64-26,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|26,44-26,70|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,31-27,33|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,47|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,44-27,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,55|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,58|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,55-27,61|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|well-formedness|27,9-27,62|Postcondition
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,21-30,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,21-31,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,21-32,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,21-33,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,39-33,39|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,13-36,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,16-36,16|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,23-36,23|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,39-36,39|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,26-41,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,42-41,42|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-26,11|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,26-32,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,47-34,47|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,63-34,63|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,71-34,71|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,74-34,74|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|25,12-25,56|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,76|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|24,12-24,23|Precondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|26,11-27,62|Postcondition
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|29,9-29,28|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,19-30,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|30,14-30,14|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|31,19-31,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,24-32,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|32,19-32,26|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,19-33,24|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|33,24-33,41|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,46|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,62|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,46-34,65|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,70|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,70-34,73|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|34,19-34,76|LoopInvariant
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,12|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,12-36,18|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,22|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,38|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|36,22-36,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|38,13-38,32|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,25|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,41|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,25-41,44|AssertionAutomatic
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|41,5-41,45|CodeLine
//::         - >-
//::           snapshot_bug_multiple_less_equal_not_covered.dfy|MinSecondValueFirst1|correctness|42,1-42,1|AssertionAutomatic
//::   calls: []
//::
