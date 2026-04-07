// ProofPulse deep-dive: lurking axioms and dependency mapping
//
// Goal of this file:
// 1) Reproduce a quantifier-heavy case where dependency attribution may be unstable.
// 2) Document the end-to-end mapping Dafny -> Boogie -> SMT (Z3) -> unsat core.
// 3) Explain how to map unsat-core atoms back to source-level spans/variables.

method LurkingAxiomsDeepDive(n: array<int>) returns (ex: array<int>)
  ensures n.Length == ex.Length
  ensures forall i: int :: 0 <= i < n.Length ==> ex[i] == 0
{
  var z := 0; // Intentionally irrelevant candidate, useful for core-sensitivity checks.
  ex := new int[n.Length];
  var i := 0;
  while i < n.Length
    invariant 0 <= i <= n.Length
    invariant forall k: int :: 0 <= k < i ==> ex[k] == 0
  {
    ex[i] := 0;
    i := i + 1;
  }
}
