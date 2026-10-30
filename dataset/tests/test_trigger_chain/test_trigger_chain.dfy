ghost predicate P(x: int)
ghost function F(x: int): int
ghost function G(x: int): int

// z3's core holds only the second precondition and the postcondition. The
// term F(a) that triggers the second precondition is created by instantiating
// the first one on G(a), which the third precondition supplies. Removing the
// first or the third precondition breaks the postcondition.
method Chain(a: int)
  requires forall x {:trigger G(x)} :: F(x) == G(x) + 1
  requires forall x {:trigger F(x)} :: P(x)
  requires G(a) > 0
  ensures P(a)
{
}

//::: Name - Trigger chain through another quantifier
//::: Description - A quantifier's instantiation creates the term that triggers the quantifier the proof uses; the quantifier and the fact supplying its own trigger term are tracked from z3's trace
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
