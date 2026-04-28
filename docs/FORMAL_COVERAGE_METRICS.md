# Formal Coverage Metrics (Testing-Inspired)

## Mapping: Testing Coverage → Formal Verification Coverage

| Testing Metric | Formal Analogue | What It Measures |
|---|---|---|
| Statement coverage | Source line proof coverage | % of proof-relevant lines used in successful proof dependencies |
| Branch coverage | Path-condition coverage | Whether both guard outcomes contribute to obligations |
| Condition coverage | Predicate-atom coverage | Atomic predicates from contracts/invariants actually needed |
| MC/DC | Minimal proof influence | Each atom independently influences proof success |
| Function coverage | Contract-call coverage | Whether callee requires/ensures are consumed by caller proofs |
| Path coverage | VC class/path coverage | Obligation classes (assert, post, inv-init, inv-preserve, termination) with explainable deps |
| Mutation score | Proof mutation score | Fraction of code/spec mutants detected by failed proofs |

## Formal-Native Metrics

| Metric | Definition |
|---|---|
| Lurking-axiom ratio | Share of obligations relying on quantified/background axioms not obvious at source |
| Redundant spec ratio | Fraction of spec clauses never needed in any successful proof |
| Vacuity ratio | Fraction of proofs discharged due to inconsistent assumptions |
| Core minimality gap | size(extracted core) − size(minimized core) |
| Granularity precision | Agreement between line-level and subexpression-level attribution |
| Solver-stability score | Attribution stability across solver versions/seeds (Jaccard overlap) |

## Code Examples

Each metric has a small Dafny example with expected output in the original document. Key patterns:

- **Vacuity**: `requires forall t:int :: t*t+1 <= t*t` makes any postcondition provable
- **Redundancy**: `ensures 1 == 1` alongside real specs → unused clause
- **Core gap**: `assert true; assert x == x;` → extracted core may include both, minimized keeps only needed
- **Lurking axioms**: `ensures forall i :: 0 <= i < a.Length ==> a[i] == a[i]` → depends on background theory

## Evaluation Plan

- Accuracy: compare with manually validated proof explanations
- Actionability: measure whether users can safely remove redundant specs
- Time impact: debugging and proof-maintenance time
- Robustness: stability across benchmark families and solver settings
- Generality: portability across Dafny, Verus, and related backends
