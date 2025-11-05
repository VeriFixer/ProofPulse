method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  assert |B| == |B'| + 1; // Assertion not essential for the prove
  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    assert A == B'; // Essential Assertion for prove
  }
}

// This test is failing a lot for assertion it has two bugs mainly
// my scripts are not considering 8,3  and 8,3-8,15 the same assertion what is breaking things
// After that there are as well a lot of other bugs

//::: Name - Assertion Complete
//::: Description - Assert Complete when is used to prove a postcondition (therefore it must really be necessary for the prove)
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - CovTest
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