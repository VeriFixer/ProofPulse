method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  assert |B| == |B'| + 1; 
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B'; // Essential Assertion for prove
  }
}

// Limitations 
// Although comenting out assertion 8 still makes verification to pass it really is being 
// highlighted in the unsat core (even with minimize options, To improve further only with scripts)
// To even extract more minimal cores possibly. But for now is working
// Line 3 is covcomplete as it is needed and used in its own recursive call

//::: Name - Assertion Complete
//::: Description - Assert Complete when is used to prove a postcondition (therefore it must really be necessary for the prove)
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovComplete
//::: L4 - CovComplete
//::: L5 - CovComplete
//::: L6 - CovComplete
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
//::: L14 - CovComplete