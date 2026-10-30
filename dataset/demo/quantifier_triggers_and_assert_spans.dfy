// Facts whose only part in a proof is to supply the term that triggers a
// quantifier. z3's unsat core leaves them out; ProofPulse finds them in z3's
// trace. Expected: every line marked "needed" is covered, every line marked
// "removable" is uncovered, and deleting a "needed" line breaks verification.

ghost predicate P(x: int)
ghost function F(x: int): int
ghost function G(x: int): int

// An assert used only as a trigger hint.
method TriggerHint(a: int)
  requires forall x {:trigger F(x)} :: P(x) && F(x) > 0  // needed
  ensures P(a)
{
  assert F(a) > 0;  // needed: supplies F(a)
}

// A precondition used only as a trigger hint.
method TriggerPrecondition(a: int)
  requires forall x {:trigger F(x)} :: P(x)  // needed
  requires F(a) > 0                         // needed: supplies F(a)
  ensures P(a)
{
}

// One quantifier's instance creates the term that triggers another.
method Chain(a: int)
  requires forall x {:trigger G(x)} :: F(x) == G(x) + 1  // needed: turns G(a) into F(a)
  requires forall x {:trigger F(x)} :: P(x)              // needed
  requires G(a) > 0                                     // needed: supplies G(a)
  ensures P(a)
{
}

// Two facts supply trigger terms, but the proof needs only one instance.
method Decoy(a: int)
  requires forall x {:trigger F(x)} :: P(x)  // needed
  requires F(a) > 0                         // needed: supplies F(a)
  requires F(a + 1) > 0                     // removable: F(a + 1) is not used
  ensures P(a)
{
}

// The same hint in a loop: keeping the invariant needs the term F(i).
method LoopHint(n: int)
  requires 0 <= n                                       // removable, with the first invariant
  requires forall x {:trigger F(x)} :: P(x) && F(x) > 0  // needed
  ensures forall k :: 0 <= k < n ==> P(k)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n  // removable: on exit i >= n is enough
    invariant forall k :: 0 <= k < i ==> P(k)
  {
    assert F(i) > 0;  // needed: supplies F(i)
    i := i + 1;
  }
}

// ---------------------------------------------------------------------------
// Assert spans. Dafny reports an assert used by a proof as "assert statement"
// over the whole expression (parentheses included), while it checks the
// conjuncts inside as separate assertions. ProofPulse now maps the use onto
// those assertions, so these asserts show as covered.

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

// Split into conjuncts: both are needed by the postcondition.
method SumThree(s: seq<int>) returns (r: int)
  requires |s| == 3
  ensures r == Sum(s)
{
  r := s[0] + s[1] + s[2];
  assert (Sum(s[2..]) == s[2] && Sum(s[1..]) == s[1] + Sum(s[2..]));  // needed
}

predicate IsSublistAt(sub: seq<int>, main: seq<int>, i: int) {
  0 <= i <= |main| - |sub| && sub == main[i .. i + |sub|]
}

// Parenthesized: the assert is the witness for the exists in the postcondition.
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures result == exists k :: IsSublistAt(sub, main, k)
{
  if |sub| > |main| {
    return false;
  }
  for i := 0 to |main| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> !IsSublistAt(sub, main, j)
  {
    if sub == main[i .. i + |sub|] {
      assert(IsSublistAt(sub, main, i));  // needed
      return true;
    }
  }
  result := false;
}
