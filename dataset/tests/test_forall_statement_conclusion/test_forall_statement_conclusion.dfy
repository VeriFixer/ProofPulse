function F(n: nat): nat { if n == 0 then 0 else F(n - 1) + 1 }

// Needs induction, which the solver does not do on its own.
lemma {:induction false} FId(n: nat)
  ensures F(n) == n
{
  if n > 0 { FId(n - 1); }
}

// Proof form: only the forall statement proves the postcondition.
lemma ProofForm(k: nat)
  ensures forall n: nat :: n < k ==> F(n) + 1 == n + 1
{
  forall n: nat | n < k
    ensures F(n) + 1 == n + 1
  {
    FId(n);
  }
}

// Call form: only the forall call proves the postcondition.
lemma CallForm(k: nat)
  ensures forall n: nat :: n < k ==> F(n) == n
{
  forall n: nat | n < k {
    FId(n);
  }
}

//::: Name - Postcondition proved by a forall statement
//::: Description - Dafny assumed the conclusion of a forall statement (both the "ensures" form and the call form) without a proof-dependency id, so the postconditions it proves looked unproved (Uncovered) and the forall's ensures clause and the call in its body looked unneeded. With the conclusion tracked they are covered. The range n < k stays Uncovered: FId(n) holds for every n.
//::: L12 - CovTest
//::: L14 - Uncovered
//::: L15 - CovComplete
//::: L23 - CovTest
//::: L26 - CovComplete
