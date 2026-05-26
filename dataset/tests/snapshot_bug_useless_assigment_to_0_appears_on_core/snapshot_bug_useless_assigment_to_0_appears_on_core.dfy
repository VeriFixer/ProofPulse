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
//:: version: 1
//:: nodes:
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,21-6,21|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 21
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 5
//::       col: 9
//::     end:
//::       line: 5
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 19
//::     end:
//::       line: 6
//::       col: 21
//::     prooftext: array size is never negative
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 6
//::       col: 5
//::     end:
//::       line: 6
//::       col: 28
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 7
//::       col: 9
//::     end:
//::       line: 7
//::       col: 15
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 9
//::       col: 19
//::     end:
//::       line: 9
//::       col: 24
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 24
//::     end:
//::       line: 10
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 19
//::     end:
//::       line: 10
//::       col: 26
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 49
//::     end:
//::       line: 11
//::       col: 49
//::     prooftext: >-
//::       variable 'ex', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 49
//::     end:
//::       line: 11
//::       col: 53
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 19
//::     end:
//::       line: 11
//::       col: 58
//::     prooftext: loop invariant
//::     isTopAssertion: false
//::     type: LoopInvariant
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 15
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 9
//::     prooftext: >-
//::       variable 'ex', which is subject to definite-assignment rules, is always
//::       initialized here
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 13
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 9
//::     end:
//::       line: 13
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovTest
//::     covStatusInternal: CovTest
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 14
//::       col: 9
//::     end:
//::       line: 14
//::       col: 19
//::     prooftext: assignment (or return)
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 15
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: false
//::     type: CodeLine
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 16
//::       col: 1
//::     end:
//::       line: 16
//::       col: 1
//::     prooftext: >-
//::       out-parameter 'ex', which is subject to definite-assignment rules, is
//::       always initialized at this return point
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,21-9,21|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
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
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,21-10,21|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 21
//::     end:
//::       line: 10
//::       col: 21
//::     prooftext: this loop invariant holds on entry
//::     isTopAssertion: true
//::     type: LoopInvariant
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,19|LoopInvariant
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
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
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,17-8,17|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 17
//::     end:
//::       line: 8
//::       col: 17
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,11-13,11|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 13
//::       col: 11
//::     end:
//::       line: 13
//::       col: 11
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-8,5|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 8
//::       col: 5
//::     end:
//::       line: 8
//::       col: 5
//::     prooftext: loop or recursion terminates
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,22-2,22|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 22
//::     end:
//::       line: 2
//::       col: 22
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,13|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 13
//::     prooftext: this postcondition holds
//::     isTopAssertion: true
//::     type: Postcondition
//::     covStatus: CovTest
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,26-10,26|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 10
//::       col: 26
//::     end:
//::       line: 10
//::       col: 26
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,51-11,51|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 11
//::       col: 51
//::     end:
//::       line: 11
//::       col: 51
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: correctness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,15-2,15|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 15
//::     end:
//::       line: 2
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 15
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 25
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 13
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 37
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 50
//::     prooftext: array is never null
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 54
//::     prooftext: index in range
//::     isTopAssertion: false
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 50
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 29
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 13
//::     end:
//::       line: 3
//::       col: 59
//::     prooftext: method ensures clause
//::     isTopAssertion: false
//::     type: Postcondition
//::     covStatus: Uncovered
//::     covStatusInternal: Uncovered
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,28-2,28|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 2
//::       col: 28
//::     end:
//::       line: 2
//::       col: 28
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,52-3,52|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 52
//::     end:
//::       line: 3
//::       col: 52
//::     prooftext: index in range
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//::   - id: >-
//::       snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,39-3,39|AssertionAutomatic
//::     file: snapshot_bug_useless_assigment_to_0_appears_on_core.dfy
//::     start:
//::       line: 3
//::       col: 39
//::     end:
//::       line: 3
//::       col: 39
//::     prooftext: target object is never null
//::     isTopAssertion: true
//::     type: AssertionAutomatic
//::     covStatus: CovComplete
//::     covStatusInternal: CovComplete
//::     methodName: zeroVector
//::     methodType: well-formedness
//::     assertionGroup: zeroVector
//:: edges:
//::   tops:
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,21-6,21|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,21-9,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,21-10,21|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,19|LoopInvariant
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,17-8,17|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,11-13,11|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-8,5|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,22-2,22|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,13|Postcondition
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,26-10,26|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,51-11,51|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,53|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|3,13-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|5,9-5,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,19-6,21|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|6,5-6,28|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|7,9-7,15|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|9,19-9,24|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,24-10,26|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|10,19-10,26|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,49-11,49|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|11,19-11,58|LoopInvariant
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,15-8,17|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,9|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,13|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|13,9-13,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|14,9-14,19|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|8,5-15,5|CodeLine
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|correctness|16,1-16,1|AssertionAutomatic
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,15-2,15|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,28-2,28|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,52-3,52|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::     - id: >-
//::         snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,39-3,39|AssertionAutomatic
//::       provedBy:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,37-3,39|AssertionAutomatic
//::       proofUnused:
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,15|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,25-2,28|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|2,13-2,28|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,39|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,50|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,54|AssertionAutomatic
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,50-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,29-3,59|Postcondition
//::         - >-
//::           snapshot_bug_useless_assigment_to_0_appears_on_core.dfy|zeroVector|well-formedness|3,13-3,59|Postcondition
//::   calls: []
//::
