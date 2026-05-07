// ProofPulse demo: bugs, limitations, and main difficulties
// This file is presentation-oriented and intentionally mixes small reproductions.

function IdBug<T>(a: T): T {
  a
}

// -----------------------------------------------------------------------------
// BUG 1: Unsat core may include redundant assumptions (non-minimal core).
// Symptom seen in practice: an irrelevant assignment can appear as used.
// Why this happens:
// - The generated SMT includes named assumptions from Boogie.
// - Z3 unsat-core extraction is not guaranteed to be minimal.
// - A larger core may include redundant assumptions (for example an assume tied
//   to an unrelated assignment), so a line can look "used" even when logically
//   unnecessary for the proof.
// - In the original investigation, disabling a specific generated assumption
//   produced a strictly smaller core, confirming non-minimal extraction.
// -----------------------------------------------------------------------------
method BugUnsatCoreNonMinimal(n: array<int>) returns (ex: array<int>)
  ensures n.Length == ex.Length
  ensures forall i: int :: 0 <= i < n.Length ==> ex[i] == 0
{
  var z := 0; // Artificially irrelevant line that may still appear in extracted core.
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