method swap(a : int, b:int) returns (c:int, d:int)
    ensures a + 1 == c
    ensures b + 1 == d
{
    c,d := a + 1,b + 1; // line appears uncovered but if split in two assigment it is covered
}

//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,19-2,19|Postcondition
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 2
//::       col: 19
//::     end:
//::       line: 2
//::       col: 19
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22|Postcondition
//::     file: snapshot_test_two_assigments_same_line.dfy
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
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23|CodeLine
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 5
//::       col: 5
//::     end:
//::       line: 5
//::       col: 23
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22|Postcondition
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 22
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1|AssertionAutomatic
//::     file: snapshot_test_two_assigments_same_line.dfy
//::     start:
//::       line: 6
//::       col: 1
//::     end:
//::       line: 6
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'c', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//::   - id: >-
//::       snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,19-3,19|Postcondition
//::     file: snapshot_test_two_assigments_same_line.dfy
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
//::     methodName: swap
//::     methodType: correctness
//::     assertionGroup: swap
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,19-2,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22|Postcondition
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23|CodeLine
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,19-3,19|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|3,13-3,22|Postcondition
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|2,13-2,22|Postcondition
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|5,5-5,23|CodeLine
//::         - >-
//::           snapshot_test_two_assigments_same_line.dfy|swap|correctness|6,1-6,1|AssertionAutomatic
//::   calls: []
//::
