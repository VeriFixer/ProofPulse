ghost predicate P(x: int)
ghost function F(x: int): int

// Both F(a) and F(a + 1) trigger the quantifier, but the postcondition only
// needs the instantiation on F(a): the third precondition can be removed.
method Decoy(a: int)
  requires forall x {:trigger F(x)} :: P(x)
  requires F(a) > 0
  requires F(a + 1) > 0
  ensures P(a)
{
}

//::: Name - Trigger term that the proof does not need
//::: Description - Only the fact whose trigger term the proof needs is tracked; a fact supplying a term for an instantiation the proof does not use stays uncovered
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - Uncovered
