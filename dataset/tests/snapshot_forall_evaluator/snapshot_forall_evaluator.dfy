method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a.Length >= 0
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    for i := 0 to a.Length
        invariant result ==> forall k :: 0 <= k < i ==> a[k] == n
    {
        if a[i] != n {
            result := false;
            break;
        }
    }
}

method Main()
{
    var a := new int[1];
    a[0] := 5;
    var r := AllElementsEqual(a, 5);
    assert(r == true);

}

//:: method AllElementsEqual:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 7
//::       col: 19
//::     end:
//::       line: 7
//::       col: 21
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
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
//::       batchResourceCount: 6446
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 26
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::       - requires clause
//::       - requires clause
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
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 3
//::       col: 24
//::     end:
//::       line: 3
//::       col: 66
//::     methodName: AllElementsEqual
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
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 12799
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 66
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 12838
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 19
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
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
//::       isProvedBy: false
//::       isUnused: true
//::     type: CodeLine
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 7
//::       col: 14
//::     end:
//::       line: 7
//::       col: 14
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::       - lower bound does not exceed upper bound
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 6715
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 19
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::       - >-
//::         variable 'result', which is subject to definite-assignment rules, is
//::         always initialized here
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 57
//::     end:
//::       line: 8
//::       col: 57
//::     methodName: AllElementsEqual
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
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 10748
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 57
//::     end:
//::       line: 8
//::       col: 60
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 10
//::       batchOutcome: Valid
//::       batchResourceCount: 10905
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 19
//::     end:
//::       line: 8
//::       col: 65
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 8
//::       col: 30
//::     end:
//::       line: 8
//::       col: 65
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 12618
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 10
//::       col: 12
//::     end:
//::       line: 10
//::       col: 12
//::     methodName: AllElementsEqual
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
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 10691
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 10
//::       col: 12
//::     end:
//::       line: 10
//::       col: 15
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::       - index in range
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 10824
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 11
//::       col: 13
//::     end:
//::       line: 11
//::       col: 28
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
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
//::   - locationId: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 15
//::       col: 1
//::     end:
//::       line: 15
//::       col: 1
//::     methodName: AllElementsEqual
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 19
//::       col: 22
//::     end:
//::       line: 19
//::       col: 22
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 5362
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 19
//::       col: 9
//::     end:
//::       line: 19
//::       col: 24
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
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
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 5
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 8267
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 8
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 11063
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 20
//::       col: 5
//::     end:
//::       line: 20
//::       col: 14
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
//::       - assignment (or return)
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
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 21
//::       col: 9
//::     end:
//::       line: 21
//::       col: 36
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - call
//::       - assignment (or return)
//::       - call
//::       - assignment (or return)
//::       - call
//::       - assignment (or return)
//::       - call
//::       - assignment (or return)
//::       - the precondition always holds
//::       - requires clause at snapshot_forall_evaluator.dfy(2,14)-(2,26) from call
//::       - call
//::       - assignment (or return)
//::       - assignment (or return)
//::       - ensures clause at snapshot_forall_evaluator.dfy(4,25)-(4,66) from call
//::       - call
//::     roles:
//::       isTop: true
//::       isCall: true
//::       isProvedBy: true
//::       isUnused: true
//::     type: Call
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 11410
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 22
//::       col: 5
//::     end:
//::       line: 22
//::       col: 22
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
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
//::       batchIndex: 6
//::       batchOutcome: Valid
//::       batchResourceCount: 16495
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|2,14-2,26
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 2
//::       col: 14
//::     end:
//::       line: 2
//::       col: 26
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - requires clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Precondition
//::     topMeta: null
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_forall_evaluator.dfy|Main|correctness|4,25-4,66
//::     file: snapshot_forall_evaluator.dfy
//::     start:
//::       line: 4
//::       col: 25
//::     end:
//::       line: 4
//::       col: 66
//::     methodName: Main
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: false
//::       isUnused: false
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//:: edges:
//::   provedBy:
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::       provers:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::       provers:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::       provers:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::       provers:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::       provers:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::       provers:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::       provers:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::   proofUnused:
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,15
//::       unused:
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|3,24-3,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|4,25-4,66
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|6,5-6,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,19-7,21
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|7,14-7,14
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,19
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,57
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,57-8,60
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,19-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|8,30-8,65
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|10,12-10,12
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|11,13-11,28
//::         - snapshot_forall_evaluator.dfy|AllElementsEqual|correctness|15,1-15,1
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::       unused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::         - snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::       unused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::         - snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::       unused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::         - snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::       unused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,9-19,24
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,14
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::         - snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::     - top: snapshot_forall_evaluator.dfy|Main|correctness|22,5-22,22
//::       unused:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|19,22-19,22
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,5
//::         - snapshot_forall_evaluator.dfy|Main|correctness|20,5-20,8
//::         - snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::   connections:
//::     - call: snapshot_forall_evaluator.dfy|Main|correctness|21,9-21,36
//::       targets:
//::         - snapshot_forall_evaluator.dfy|Main|correctness|2,14-2,26
//::         - snapshot_forall_evaluator.dfy|Main|correctness|4,25-4,66
//::
