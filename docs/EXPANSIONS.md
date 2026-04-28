# Expansion Roadmap

## Core Goals

1. **Lurking-axiom tracking** — detect obligations discharged via non-obvious quantified facts, triggers, or solver axioms rather than explicit source intent.

2. **Complete language feature support** — handle all Dafny constructs.

3. **Subexpression-level attribution** — move beyond line-level to expression/conjunct/bound-level dependency mapping.

4. **Z3 core minimization** — reduce non-minimal unsat cores. Compare baseline vs shrinking heuristics. `forceMinimization` option now implemented through the full stack (core → VSCode → eval CLI → test CLI). Comparison mode (`--compare-minimization`) runs entries twice and diffs classifications + timing.

5. **User studies** — measure whether explanations reduce debugging time and improve proof-maintenance decisions.

6. **VSCode integration** — done. Extension provides gutter decorations, inline coverage coloring, hover diagnostics.

## Formal Coverage Metrics Idea

See `docs/FORMAL_COVERAGE_METRICS.md` for testing-inspired formal coverage metrics.
