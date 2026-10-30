ghost predicate P(x: int)
ghost function F(x: int): int

// The assert is proved from the precondition, and its only part in the
// postcondition's proof is the term F(a), which triggers the quantifier.
method TriggerHint(a: int)
  requires forall x {:trigger F(x)} :: P(x) && F(x) > 0
  ensures P(a)
{
  assert F(a) > 0;
}

// The second precondition only supplies the term F(a).
method TriggerPrecondition(a: int)
  requires forall x {:trigger F(x)} :: P(x)
  requires F(a) > 0
  ensures P(a)
{
}

//::: Name - Facts that only supply a trigger term
//::: Description - z3's unsat core leaves out a fact whose only part in the proof is the term that triggers a quantifier; removing it breaks verification, so it is tracked from z3's trace
//::: L10 - CovComplete
//::: L16 - CovComplete
