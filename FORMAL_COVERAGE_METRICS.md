# Formal Coverage Metrics Inspired by Software Testing

This note expands testing coverage concepts into formal-verification coverage concepts, with examples and extraction ideas.

## 1) Statement Coverage -> Source Line Proof Coverage
Testing definition:
- Percentage of executable statements run by tests.

Testing example:
- Code has 100 statements.
- Test suite executes 78 statements.
- Statement coverage = 78%.

Formal analogue:
- Percentage of source lines that are actually used to discharge proof obligations.

Formal example:
- Method has 20 relevant lines (code + assertions + contracts).
- Unsat-core/source mapping shows 12 lines used in successful proofs.
- Proof line coverage = 60%.

How to extract:
- Map source spans to IVL IDs and SMT named assumptions.
- Collect lines that appear in dependency sets across all VCs.
- Compute used_lines / candidate_lines.

Code example (4-5 lines):
```dafny
method M(x: int) returns (y: int)
	ensures y >= x
{ y := x + 1; assert y >= x; }
```

Expected metric output on this snippet:
- Candidate proof-relevant lines: 2 (`y := x + 1`, `assert y >= x`).
- Used lines (likely): 2.
- Source line proof coverage: about 100%.

## 2) Branch Coverage -> Path-Condition Coverage
Testing definition:
- Whether each branch outcome (`if` true/false, match arms) has been executed.

Testing example:
- 10 branches total, both sides covered for 7 branches.
- Branch coverage = 70%.

Formal analogue:
- Whether each control-flow guard contributes to at least one discharged obligation.

Formal example:
- Guard `x < 0` exists, but only positive path contributes to proof.
- Report: true-side used, false-side unused for proof.

How to extract:
- Track guard-origin IDs in generated VCs.
- Mark guard side as covered when the corresponding assumption appears in proof dependency traces.
- Aggregate per branch and side.

Code example (4-5 lines):
```dafny
method BranchDemo(x: int) returns (y: int)
	ensures x < 0 ==> y == -x
	ensures x >= 0 ==> y == x
{ if x < 0 { y := -x; } else { y := x; } }
```

Expected metric output on this snippet:
- One branch guard with two sides.
- Both sides contribute to separate postconditions.
- Path-condition coverage: 2/2 sides covered (100%).

## 3) Condition Coverage -> Predicate-Atom Coverage
Testing definition:
- Whether each boolean subcondition has evaluated to true/false.

Testing example:
- Condition `(a && b)`; tests only vary `a`, never vary `b`.
- Condition coverage incomplete.

Formal analogue:
- Whether each atomic predicate in contracts/invariants/assertions is actually needed in proofs.

Formal example:
- Invariant: `0 <= i <= n && s == i`.
- Dependencies use `s == i` and `i <= n`, but never `0 <= i`.
- Atom-level report marks one atom unused.

How to extract:
- Parse spec predicates into atomic subexpressions.
- Build mapping from atoms to SMT assumptions/lemmas.
- Attribute atom usage from unsat cores or proof traces.

Code example (4-5 lines):
```dafny
method CondDemo(i: int, n: int)
	requires i < n && n <= 100
{ assert i < 100; }
```

Expected metric output on this snippet:
- Candidate atoms: `i < n`, `n <= 100`.
- Both atoms are needed to derive `i < 100`.
- Predicate-atom coverage: 2/2 used (100%).

## 4) MC/DC -> Minimal Proof Influence Coverage
Testing definition:
- Each condition independently affects decision outcome while others fixed.

Testing example:
- Decision `A || B`.
- Need tests showing A alone flips outcome and B alone flips outcome.

Formal analogue:
- Each atomic condition independently affects proof success/failure.

Formal example:
- Postcondition proof depends on `(x >= 0)` and `(x <= n)`.
- If removing either atom separately causes proof failure, both are independently influential.

How to extract:
- Run delta checks by dropping/toggling one atom at a time in verification context.
- Observe VC status change (`valid` -> `unknown`/`invalid`).
- Record influence matrix per decision/goal.

Code example (4-5 lines):
```dafny
method MCDC(x: int, n: int)
	requires x <= n && 0 <= n
	ensures 0 <= x ==> x <= n
{ }
```

Expected metric output on this snippet:
- Candidate atoms: `x <= n`, `0 <= n` for proving `0 <= x ==> x <= n`.
- `x <= n` is influential (dropping it breaks the proof).
- `0 <= n` is non-influential for this goal (dropping it keeps proof valid).
- Minimal proof influence coverage: 1/2 influential atoms (50%).

## 5) Function Coverage -> Contract-Call Coverage
Testing definition:
- Whether each function was called by tests.

Testing example:
- 20 functions, 15 called by at least one test.
- Function coverage = 75%.

Formal analogue:
- Whether called contracts (`requires`/`ensures`) are actually consumed by downstream proofs.

Formal example:
- A callee ensures `x == 32`.
- Caller proof uses this ensures in assertion discharge.
- Mark this call-contract pair as covered.

How to extract:
- Map call-site IDs and callee postcondition IDs.
- Detect merged or linked SMT atoms (e.g., call+ensures IDs).
- Mark contract call covered when used in core/trace.

Code example (4-5 lines):
```dafny
method Ret32() returns (x: int)
	ensures x == 32
{ x := 32; }
method UseRet32() { var n := Ret32(); assert n == 32; }
```

Expected metric output on this snippet:
- One call with one meaningful ensures.
- Caller assertion consumes callee ensures.
- Contract-call coverage: 1/1 covered (100%).

## 6) Path Coverage -> VC Path Coverage
Testing definition:
- Whether different execution paths are tested.

Testing example:
- 12 relevant paths, 5 exercised.
- Path coverage = 41.7%.

Formal analogue:
- Whether distinct VC obligation paths/classes are explained by source dependencies.

Formal example:
- Loop generates obligations for init, preserve, and post-use.
- Tool explains init+post-use but preserve has weak attribution.

How to extract:
- Classify obligations by type and origin (assertion, invariant init/preserve, postcondition, termination).
- For each class/path, check if mapping to source dependencies is complete.
- Report explained_paths / total_paths.

Code example (4-5 lines):
```dafny
method LoopPath(n: nat)
{ var i := 0;
  while i < n
	invariant 0 <= i <= n
    decreases n - i
  { i := i + 1; } }
```

Expected metric output on this snippet:
- VC classes present: invariant-init, invariant-preservation, loop-exit-to-post, termination-decrease.
- If all four classes are mapped to source spans, VC path coverage is 4/4 (100%).
- If one class is missing attribution (for example preservation), coverage is 3/4 (75%).

## 7) Mutation Score -> Proof Mutation Score
Testing definition:
- Fraction of mutants killed by tests.

Testing example:
- 100 mutants, 83 killed.
- Mutation score = 83%.

Formal analogue:
- Fraction of code/spec mutations detected by proof failure or significant dependency shifts.

Formal example:
- Change `<=` to `<` in invariant.
- If verification fails or critical dependency set changes meaningfully, mutant is detected.

How to extract:
- Generate controlled mutants for code/spec expressions.
- Re-verify and compare result + dependency graph.
- Count detected_mutants / total_mutants.

Code example (4-5 lines):
```dafny
method MutantDemo(x: int) returns (y: int)
	ensures x >= 0 ==> y == x
{ y := x; }
```

Expected metric output on this snippet:
- Example mutant: change body to `y := x + 1`.
- Mutant should be detected (postcondition fails for nonnegative `x`).
- Proof mutation score on this 1-mutant set: 1/1 (100%).

## Additional formal-native metrics

### Lurking-Axiom Dependency Ratio
- Definition: share of obligations that rely on quantified/background axioms not obvious at source.
- Extraction: tag dependencies coming from quantified axioms/triggers/background theory assumptions.

Code example (4-5 lines):
```dafny
method Lurk(a: array<int>)
	ensures forall i :: 0 <= i < a.Length ==> a[i] == a[i]
{ }
```

Expected metric output on this snippet:
- Goal is quantifier/theory-heavy but semantically trivial.
- If dependency trace points mostly to background axioms, ratio is high.
- Lurking-axiom dependency ratio: high (close to 1.0) in many encodings.

### Redundant Spec Ratio
- Definition: fraction of spec clauses never needed in any successful proof.
- Extraction: clause-level usage union over all obligations.

Code example (4-5 lines):
```dafny
method RedundantSpec(x: int) returns (y: int)
	ensures 1 == 1
	ensures y == x
{ y := x; }
```

Expected metric output on this snippet:
- Two ensures clauses, only one is semantically informative.
- Used spec clauses likely: `y == x`; unused likely: `1 == 1`.
- Redundant spec ratio: 1/2 (50%).

### Vacuity Ratio
- Definition: fraction of proofs discharged due to inconsistent assumptions or impossible preconditions.
- Extraction: contradiction checks on assumption sets + vacuity heuristics.

Code example (4-5 lines):
```dafny
method Vacuous(x: int)
	requires forall t:int :: t*t + 1 <= t*t
	ensures false
{ }
```

Expected metric output on this snippet:
- Preconditions are inconsistent, so any postcondition is provable.
- This obligation should be flagged as vacuous.
- Vacuity ratio for this single proof: 1/1 (100%).

### Core Minimality Gap
- Definition: size(extracted core) - size(minimized core).
- Extraction: run shrinking procedure over candidate assumptions; compare sizes.

Code example (4-5 lines):
```dafny
method CoreGap(x: int)
	ensures x == x
{ assert true; assert x == x; }
```

Expected metric output on this snippet:
- Extracted core may include both assertions in non-minimal settings.
- Minimized core should keep only facts needed for `x == x` (possibly none beyond tautology machinery).
- Core minimality gap: nonnegative; often > 0 when redundant assumptions appear.

### Granularity Precision
- Definition: agreement between line-level attribution and subexpression-level attribution.
- Extraction: compare coarse and fine mappings against manual oracle on sample set.

Code example (4-5 lines):
```dafny
method Granular(i: int, n: int)
	requires 0 <= i && i < n
{ assert 0 <= i; assert i < n; }
```

Expected metric output on this snippet:
- Line-level marks both asserts used.
- Subexpression-level marks each atom separately used.
- Granularity precision: high (close to perfect agreement) on this simple case.

### Solver-Stability Score
- Definition: attribution stability across solver versions/options/random seeds.
- Extraction: rerun verification matrix; compute overlap (e.g., Jaccard) of dependency sets.

Code example (4-5 lines):
```dafny
method Stable(x: int)
	ensures x + 0 == x
{ assert x + 0 == x; }
```

Expected metric output on this snippet:
- Arithmetic simplification is stable across solver settings.
- Dependency sets should vary little across seeds/options.
- Solver-stability score: high (Jaccard near 1.0).

## Practical evaluation plan (brief)
- Accuracy: compare with manually validated proof explanations.
- Actionability: measure whether users can remove redundant specs safely.
- Time impact: debugging time and proof-maintenance time.
- Robustness: stability across benchmark families and solver settings.
- Generality: portability across Dafny, Verus, and related backends.
