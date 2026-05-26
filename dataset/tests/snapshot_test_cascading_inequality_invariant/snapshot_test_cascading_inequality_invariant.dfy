method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists j :: 0 <= j < i && s[j] == k)
    {
        if s[i] == k {
            result := true;
            break;
        }
    }
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 5
//::       col: 14
//::     end:
//::       line: 5
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 5
//::       col: 14
//::     end:
//::       line: 5
//::       col: 14
//::     prooftext: lower bound does not exceed upper bound
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 30
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 4
//::       col: 5
//::     end:
//::       line: 4
//::       col: 20
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 31
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 24
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 24
//::     end:
//::       line: 6
//::       col: 31
//::     prooftext: loop invariant always holds
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 19
//::     prooftext: >-
//::       variable 'result', which is subject to definite-assignment rules, is
//::       always initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 58
//::     end:
//::       line: 7
//::       col: 61
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 67
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 9
//::       col: 12
//::     end:
//::       line: 9
//::       col: 15
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 10
//::       col: 13
//::     end:
//::       line: 10
//::       col: 27
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 14
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'result', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,21-6,21|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 21
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,26-6,26|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 6
//::       col: 26
//::     end:
//::       line: 6
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,26-7,26|LoopInvariant
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 26
//::     end:
//::       line: 7
//::       col: 26
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,13-9,13|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 9
//::       col: 13
//::     end:
//::       line: 9
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,20-2,20|Postcondition
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 2
//::       col: 20
//::     end:
//::       line: 2
//::       col: 20
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//::   - id: >-
//::       snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,59-7,59|AssertionAutomatic
//::     file: snapshot_test_cascading_inequality_invariant.dfy
//::     start:
//::       line: 7
//::       col: 59
//::     end:
//::       line: 7
//::       col: 59
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: ContainsK
//::     methodType: correctness
//::     assertionGroup: ContainsK
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,21-6,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,26-6,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,26-7,26|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,13-9,13|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,20-2,20|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,59-7,59|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,58-7,61|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|2,13-2,30|Postcondition
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|4,5-4,20|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|5,14-5,14|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,19-6,24|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|6,24-6,31|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,19|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|7,19-7,67|LoopInvariant
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|9,12-9,15|AssertionAutomatic
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|10,13-10,27|CodeLine
//::         - >-
//::           snapshot_test_cascading_inequality_invariant.dfy|ContainsK|correctness|14,1-14,1|AssertionAutomatic
//::   calls: []
//::
