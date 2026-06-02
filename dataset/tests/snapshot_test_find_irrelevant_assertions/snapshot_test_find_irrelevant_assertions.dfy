method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  assert(43 == 43); 

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
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 5
//::       col: 3
//::     end:
//::       line: 5
//::       col: 19
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionManual
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 3236
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 2
//::       col: 20
//::     end:
//::       line: 2
//::       col: 23
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 5534
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24
//::     file: snapshot_test_find_irrelevant_assertions.dfy
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
//::       batchIndex: 3
//::       batchOutcome: Valid
//::       batchResourceCount: 5616
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 12
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 10
//::       col: 5
//::     end:
//::       line: 10
//::       col: 15
//::     methodName: Abs
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 12
//::       col: 1
//::     end:
//::       line: 12
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
//::   - locationId: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|14,1-16,1
//::     file: snapshot_test_find_irrelevant_assertions.dfy
//::     start:
//::       line: 14
//::       col: 1
//::     end:
//::       line: 16
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
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23
//::       provers:
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|14,1-16,1
//::     - top: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24
//::       provers:
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12
//::   proofUnused:
//::     - top: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19
//::       unused:
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1
//::     - top: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23
//::       unused:
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|8,5-8,12
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1
//::     - top: snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|3,19-3,24
//::       unused:
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|2,20-2,23
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|5,3-5,19
//::         - >-
//::           snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|10,5-10,15
//::         - snapshot_test_find_irrelevant_assertions.dfy|Abs|correctness|12,1-12,1
//::   connections: []
//::
