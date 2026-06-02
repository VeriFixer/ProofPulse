method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := x; // Line never covered bug report opened
  }
}

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 2
//::       col: 20
//::     end:
//::       line: 2
//::       col: 23
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 4000
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 11
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 3
//::       col: 19
//::     end:
//::       line: 3
//::       col: 24
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 4222
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 12
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1
//::     file: snapshot_bug_assigment_never_covered.dfy
//::     start:
//::       line: 10
//::       col: 1
//::     end:
//::       line: 10
//::       col: 1
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'y', which is subject to definite-assignment rules, is
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
//::     - top: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23
//::       provers:
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11
//::     - top: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24
//::       provers:
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12
//::   proofUnused:
//::     - top: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23
//::       unused:
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|6,5-6,12
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1
//::     - top: snapshot_bug_assigment_never_covered.dfy|Abs|correctness|3,19-3,24
//::       unused:
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|2,20-2,23
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|8,5-8,11
//::         - snapshot_bug_assigment_never_covered.dfy|Abs|correctness|10,1-10,1
//::   connections: []
//::
