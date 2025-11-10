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

//::: Name - Repeated assertion in proofCore Extraction
//::: To see this tested why was found you must see L5 and uncomment that line (it appears on the core of assertion on line 9)
//::: I think it is because of the bug
//::: L5 - Uncovered