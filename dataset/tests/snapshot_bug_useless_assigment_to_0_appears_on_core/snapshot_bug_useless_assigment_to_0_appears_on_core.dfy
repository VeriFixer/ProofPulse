method zeroVector(n : array<int>) returns (ex:array<int>)
    ensures n.Length == ex.Length
    ensures forall i:int :: 0<= i < n.Length ==> ex[i] == 0
{
    var z:= 0 ;  // If z equals 0 this line appears covered, if equals something differn appears uncovered! (covering line 9 ! weird) 
    ex := new int[n.Length];
    var i := 0;
    while(i < n.Length)
        invariant 0 <= i 
        invariant i <= n.Length
        invariant forall k:int :: 0<= k < i ==> ex[k] == 0
    {
        ex[i] := 0;
        i := i + 1;
    }
}
// L5 appears covered, The problem is that with that line the following proof oligations are created
// Investigation_v2 makes the resoning of what happen
// inserting 0 or 123445 was completly indiferent for the z3 encodings, the unsat core
// produced by z3 was what chnaged
// if we insert the option 
//(set-option :produce-proofs true) on z3 
// it is enough to make the z3 less agresive in optimizations and the core to have more realiable the essential parts
// at least setting this solved the probblem

// I setted bug it did not work and now appears to be used in forall 
// line 11, obviously it is not.
// Cannot at all find and correct the cause of this bogey or find why it appears
// It seems to be the bug that is by far the deeest, the encodings where correct to the SMT no differnece between
// passing z := 0 or z := 1234. Therefore it must be something more prevasive


// I have fully identified the issue: Z3 is not producing a minimal unsat core.
// The SMT file contains named assumptions, such as:
// ;(assert (! $generated@@182))

// This particular line corresponds to an assume statement in the original Boogie program.
// When this line is commented out, the unsat core that Z3 extracts is:

// (aux$$assume$$id14 aux$$assume$$id28$assume_in_body aux$$assume$$id35 aux$$assume$$id36 aux$$assume$$id37 aux$$assert$$id28$maintained)

// However, if I uncomment that line (forcing Z3 not to use that clause), the resulting core becomes:

// (aux$$assume$$id28$assume_in_body aux$$assume$$id35 aux$$assume$$id36 aux$$assume$$id37 aux$$assert$$id28$maintained)

// This version is smaller and does not include the assumption aux$$assume$$id14.

// Conclusion
// The difference shows that Z3’s unsat core extraction includes redundant assumptions — it does not always minimize the core by default. When the problematic clause ($generated@@182) is disabled, Z3 produces a smaller and cleaner core, confirming that the initial core was non-minimal.


// Even with emmit prove did not help 
// investigation_v2.txt contins at the end the final solution
// The proof extracted is not minimal by z3 (and it is letting that clause slip by)
// To solve this will have to hava a guarantee of minimization

//:: method Graph:
//:: version: 2
//:: nodes:
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 15
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchResourceCount: 6742
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 25
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 6861
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 37
//::     end:
//::       line: 3
//::       col: 39
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 5
//::       batchOutcome: Valid
//::       batchResourceCount: 8368
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 39
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::       - method ensures clause
//::     roles:
//::       isTop: false
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta: null
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 50
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchResourceCount: 8907
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 54
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
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
//::       batchIndex: 4
//::       batchOutcome: Valid
//::       batchResourceCount: 9363
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 59
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 59
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
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
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     prooftexts:
//::       - method ensures clause
//::       - method ensures clause
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - array size is never negative
//::       - array size is never negative
//::       - target object is never null
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::       - target object is never null
//::       - array size is never negative
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 2
//::       batchOutcome: Valid
//::       batchResourceCount: 6484
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       batchIndex: 15
//::       batchOutcome: Valid
//::       batchResourceCount: 14201
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
//::       - ensures clause
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
//::       - ensures clause
//::       - ensures clause
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: Postcondition
//::     topMeta:
//::       batchIndex: 16
//::       batchOutcome: Valid
//::       batchResourceCount: 15214
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 15
//::     methodName: zeroVector
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 28
//::     methodName: zeroVector
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 15
//::     methodName: zeroVector
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 24
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
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
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
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
//::       - loop invariant
//::       - loop invariant always holds
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
//::     topMeta:
//::       batchIndex: 12
//::       batchOutcome: Valid
//::       batchResourceCount: 15764
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 24
//::     end:
//::       line: 10
//::       col: 26
//::     methodName: zeroVector
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
//::       batchIndex: 17
//::       batchOutcome: Valid
//::       batchResourceCount: 13190
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 26
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
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
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant is maintained by the loop
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
//::     topMeta:
//::       batchIndex: 13
//::       batchOutcome: Valid
//::       batchResourceCount: 15944
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 49
//::     end:
//::       line: 11
//::       col: 49
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 19
//::       batchOutcome: Valid
//::       batchResourceCount: 13874
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 49
//::     end:
//::       line: 11
//::       col: 53
//::     methodName: zeroVector
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
//::       batchIndex: 20
//::       batchOutcome: Valid
//::       batchResourceCount: 14432
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 58
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - loop invariant
//::       - loop invariant always holds
//::       - this loop invariant holds on entry
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
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: LoopInvariant
//::     topMeta:
//::       batchIndex: 14
//::       batchOutcome: Valid
//::       batchResourceCount: 20254
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 17
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::       - target object is never null
//::       - target object is never null
//::       - decreases expression is bounded below by 0
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 18
//::       batchOutcome: Valid
//::       batchResourceCount: 14728
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 9
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - array is never null
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::       - >-
//::         variable 'ex', which is subject to definite-assignment rules, is always
//::         initialized here
//::       - array is never null
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 7
//::       batchOutcome: Valid
//::       batchResourceCount: 14348
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 13
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
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
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
//::       - index in range
//::       - array location is in the enclosing context's modifies clause
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
//::       batchIndex: 9
//::       batchOutcome: Valid
//::       batchResourceCount: 14868
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 19
//::     methodName: zeroVector
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 14
//::       col: 9
//::     end:
//::       line: 14
//::       col: 19
//::     methodName: zeroVector
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
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 15
//::       col: 5
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::       - loop or recursion terminates
//::     roles:
//::       isTop: true
//::       isCall: false
//::       isProvedBy: true
//::       isUnused: true
//::     type: AssertionAutomatic
//::     topMeta:
//::       batchIndex: 11
//::       batchOutcome: Valid
//::       batchResourceCount: 15574
//::     covStatus: CovComplete
//::     covStatusInternal: CovTest
//::   - locationId: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 16
//::       col: 1
//::     end:
//::       line: 16
//::       col: 1
//::     methodName: zeroVector
//::     methodType: correctness
//::     prooftexts:
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
//::         always initialized at this return point
//::       - >-
//::         out-parameter 'ex', which is subject to definite-assignment rules, is
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
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::       provers:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::   proofUnused:
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::     - top: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5
//::       unused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1
//::   connections: []
//::
