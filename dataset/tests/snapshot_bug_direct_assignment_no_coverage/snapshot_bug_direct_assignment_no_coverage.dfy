method Max(a: int, b: int) returns (max: int)
    ensures max >= a && max >= b
    ensures max == a || max == b
{
    if a >= b {
        max := a;
    } else {
        max := b;
    }
}


//:: method Graph:
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,17-2,17|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 17
//::     end:
//::       line: 2
//::       col: 17
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 20
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 25
//::     end:
//::       line: 2
//::       col: 32
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 32
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17|CodeLine
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 6
//::       col: 9
//::     end:
//::       line: 6
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17|CodeLine
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 8
//::       col: 9
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1|AssertionAutomatic
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'max', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,29-2,29|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 2
//::       col: 29
//::     end:
//::       line: 2
//::       col: 29
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//::   - id: >-
//::       snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,22-3,22|Postcondition
//::     file: snapshot_bug_direct_assignment_no_coverage.dfy
//::     start:
//::       line: 3
//::       col: 22
//::     end:
//::       line: 3
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: Max
//::     methodType: correctness
//::     assertionGroup: Max
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,17-2,17|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,29-2,29|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,22-3,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|3,13-3,32|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,13-2,20|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|2,25-2,32|Postcondition
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|6,9-6,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|8,9-8,17|CodeLine
//::         - >-
//::           snapshot_bug_direct_assignment_no_coverage.dfy|Max|correctness|10,1-10,1|AssertionAutomatic
//::   calls: []
//::
