predicate IsSublistAt(sub: seq<int>, main: seq<int>, i: int) {
    0 <= i <= |main| - |sub| && sub == main[i .. i + |sub|]
}

method IsSublist ( sub : seq < int > , main : seq < int >) returns ( result : bool )
    ensures result == exists k  :: IsSublistAt(sub, main, k)
{
    if | sub | > | main | {
        return false ;
    }
    
    result := false ;

    for i := 0 to |main| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> !IsSublistAt(sub, main, j)
    {
        if sub == main[i .. i + |sub|] {
            assert(IsSublistAt(sub,main,i));
            return true;
        }
    }

    result := false ;
}


//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 14
//::       col: 14
//::     end:
//::       line: 14
//::       col: 14
//::     methodName: IsSublist
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
//::       - lower bound does not exceed upper bound
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 1
//::       batchOutcome: Valid
//::       batchResourceCount: 7161
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 8
//::       col: 8
//::     end:
//::       line: 8
//::       col: 25
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 6
//::       col: 13
//::     end:
//::       line: 6
//::       col: 60
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - this postcondition holds
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
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 11579
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 9
//::       col: 9
//::     end:
//::       line: 9
//::       col: 22
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
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
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 12
//::       col: 5
//::     end:
//::       line: 12
//::       col: 21
//::     methodName: IsSublist
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
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 15
//::       col: 19
//::     end:
//::       line: 15
//::       col: 71
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
//::       - loop invariant always holds
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 20241
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 17
//::       col: 19
//::     end:
//::       line: 17
//::       col: 38
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - upper bound within range of sequence
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::       - lower bound in range
//::       - upper bound within range of sequence
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     usedByNumber: 0
//::     topMeta:
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 13649
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 18
//::       col: 20
//::     end:
//::       line: 18
//::       col: 42
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
//::       - assertion always holds
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
//::     usedByNumber: 1
//::     topMeta:
//::       batchIndex: 8
//::       batchOutcome: Valid
//::       batchResourceCount: 14233
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 19
//::       col: 13
//::     end:
//::       line: 19
//::       col: 24
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
//::       - assignment (or return)
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
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
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 17
//::       col: 12
//::     end:
//::       line: 17
//::       col: 38
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::       - condition atom
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Condition
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 23
//::       col: 5
//::     end:
//::       line: 23
//::       col: 21
//::     methodName: IsSublist
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
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 24
//::       col: 1
//::     end:
//::       line: 24
//::       col: 1
//::     methodName: IsSublist
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
//::       - >-
//::         out-parameter 'result', which is subject to definite-assignment rules,
//::         is always initialized at this return point
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
//::   - locationId: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|1,1-3,1
//::     file: snapshot_test_assert_parenthesized.dfy
//::     start:
//::       line: 1
//::       col: 1
//::     end:
//::       line: 3
//::       col: 1
//::     methodName: IsSublist
//::     methodType: correctness
//::     prooftexts:
//::       - function definition for IsSublistAt
//::       - function definition for IsSublistAt
//::       - function definition for IsSublistAt
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: false
//::     type: CodeLine
//::     usedByNumber: 2
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//:: edges:
//::   provedBy:
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::       provers:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::       provers:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|1,1-3,1
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::       provers:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|1,1-3,1
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::       provers:
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::   proofUnused:
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::       unused:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::       unused:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::       unused:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::       unused:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::     - top: snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::       unused:
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|6,13-6,60
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|9,9-9,22
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|8,8-8,25
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|12,5-12,21
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|14,14-14,14
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|15,19-15,71
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,19-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|18,20-18,42
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|19,13-19,24
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|17,12-17,38
//::         - >-
//::           snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|23,5-23,21
//::         - snapshot_test_assert_parenthesized.dfy|IsSublist|correctness|24,1-24,1
//::   connections: []
//::
