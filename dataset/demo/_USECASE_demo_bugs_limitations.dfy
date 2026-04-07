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

// -----------------------------------------------------------------------------
// BUG 2: Assignment/call mapping inconsistencies in coverage pipeline.
// Based on cases where assignments in simple branches/calls were misclassified.
// Why this happens:
// - Direct assigments are not translated with the infrastructure Boogie -> Z3 necessary to track it
// - The final coverage mapping can miss direct attribution to the source line,
//   so a line that clearly contributes may be reported as uncovered.
// - This was observed in the original "assignment never covered" testcase.
// -----------------------------------------------------------------------------
method BugAssignmentCoverage(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x < 0 {
    y := -x;
  } else {
    y := x; // Historically observed as problematic in one bug testcase.
  }
}

// -----------------------------------------------------------------------------
// BUG 3: Method call information can be merged with ensures in low-level IDs.
// Symptom: call itself may look unused even when postcondition is required.
// Why this happens:
// - In the lowered Boogie/SMT encoding, call-site and ensures information can be
//   represented by merged internal identifiers (for example id1 + id5 style ids).
// - The unsat core can reference only the merged entity, while source mapping
//   still expects separate call and ensures attribution.
// - Result: proof dependency shows ensures-from-call, but the call token itself
//   can still appear as "unused by proof" in reports.
// -----------------------------------------------------------------------------
method Ret32WithPre(a: int) returns (x: int)
  requires a < 10
  ensures x == 32
{
  x := 32;
}

method BugCallMergedIdsMain()
{
  var n := Ret32WithPre(5);
  assert n == 32;
}

// -----------------------------------------------------------------------------
// BUG 4: Lurking axioms / quantified obligations can hide true dependencies.
// Symptom: a line or invariant can be marked as uncovered/irrelevant even when
// it is expected to be part of the proof story.
// Why this happens:
// - Quantifier-heavy verification conditions are encoded with triggers/patterns.
// - The solver can satisfy goals through alternative axiom instantiations,
//   making the final core sensitive to encoding details and search heuristics.
// - In practice this creates unstable dependency attribution for some lines.
// -----------------------------------------------------------------------------
method BugLurkingAxioms(n: array<int>) returns (ex: array<int>)
  ensures n.Length == ex.Length
  ensures forall i: int :: 0 <= i < n.Length ==> ex[i] == 0
{
  var z := 0;
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

// -----------------------------------------------------------------------------
// LIMITATION 1: Allocation translation through havoc/new can reduce traceability.
// Symptom: allocation-related lines are harder to attribute directly.
// -----------------------------------------------------------------------------
method LimitationAllocation(a: array<int>) returns (c: array<int>)
  requires a.Length > 0
  ensures c.Length == a.Length
  ensures c[0] == a[0] + 1
{
  c := new int[a.Length];
  c[0] := a[0] + 1;
}
