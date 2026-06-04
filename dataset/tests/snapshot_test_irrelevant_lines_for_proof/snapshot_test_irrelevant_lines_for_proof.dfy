method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if(x == 0){
    y := 0; // Unused by proof  _USECASE_find_irrelevant_lines.dfy(6,5)-(6,11): assignment (or return)
  }

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}



//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|2,20-2,23
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 5818
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|12,5-12,15
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 15
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
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|16,1-18,1
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
//::     start:
//::       line: 16
//::       col: 1
//::     end:
//::       line: 18
//::       col: 1
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - function definition for Id
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|3,19-3,24
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
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
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 5868
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|6,5-6,11
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 11
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|10,5-10,12
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
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
//::     usedByNumber: 1
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|14,1-14,1
//::     file: snapshot_test_irrelevant_lines_for_proof.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 14
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
//::     usedByNumber: 0
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|2,20-2,23
//::       provers:
//::         - >-
//::           snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|12,5-12,15
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|16,1-18,1
//::     - top: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|3,19-3,24
//::       provers:
//::         - >-
//::           snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|10,5-10,12
//::   proofUnused:
//::     - top: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|2,20-2,23
//::       unused:
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|3,19-3,24
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|6,5-6,11
//::         - >-
//::           snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|10,5-10,12
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|14,1-14,1
//::     - top: snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|3,19-3,24
//::       unused:
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|2,20-2,23
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|6,5-6,11
//::         - >-
//::           snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|12,5-12,15
//::         - snapshot_test_irrelevant_lines_for_proof.dfy|Abs|correctness|14,1-14,1
//::   connections: []
//::
