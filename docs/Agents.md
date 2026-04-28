# Agent Reference — ProofPulse

## What This Project Does

Analyzes Dafny verification logs → proof dependency graph → coverage status per line/token. Classifies specs as strong/weak/error. VSCode extension + web viewer + evaluation benchmark.

## Repo Layout

```
core/                   # @proofpulse/core — TS lib (parseProof, runDafny, coverage, types)
core/scripts/           # z3-minimizer-wrapper.sh, minimize_unsat_core_trace.py
vscode_extension/       # VSCode extension (gutter + inline decorations, hover, context menu)
evaluation/             # Benchmark CLI against dafny-synthesis oracle
web_viewer/             # Web server, viewer, test CLI (test_logic.js)
tests/                  # All tests (unit/, property/, integration/, test_data/)
dataset/tests/          # .dfy test files with expected annotations
dafny-synthesis/        # Git submodule — benchmark dataset
```

## Build & Test

```bash
npm run build:core                              # Build core TS → dist/
npm run build:viewer                            # Bundle spans_provider.js
npm run test:property                           # Property tests (vitest + fast-check)
npm test -w evaluation                          # Eval tests (vitest)
node web_viewer/test_logic.js                   # .dfy regression suite
node --test tests/unit/web_viewer/server.test.js  # Server unit tests
npx tsx evaluation/src/cli.ts --dataset all     # Full benchmark
```

## Key Types

- `DafnyOptions` — `{ dafnyPath?, timeoutSeconds?, forceMinimization? }`
- `DafnyResult` — `{ log, exitCode, error?, timedOut? }`
- `CovStatus` — `CovComplete | CovTest | Uncovered`
- `TokenType` — `Postcondition | Precondition | AssertionManual | AssertionAutomatic | CodeLine`
- `BenchmarkOptions` — includes `forceMinimization?`, `compareMinimization?`
- `ComparisonResults` — `{ entries, changedResults, addedTimeMs, slowdownFactor, testComparison, ... }`

## Core API

- `parseProof(sourceCode, proverLog)` → `Proof` with `ProofGraph` + `lineStatus`
- `runDafny(filePath, options?)` → `DafnyResult`
- `computeLineStatus(graph, sourceCode)` → per-line coverage
- `serializeProofGraph` / `deserializeProofGraph` — JSON round-trip

## forceMinimization Flow

When `forceMinimization: true`:
1. `dafny-runner.ts` appends `/z3exe:<wrapper>` to `--boogie` args
2. Sets env: `PROOFPULSE_Z3_PATH`, `PROOFPULSE_MINIMIZER_SCRIPT`
3. Wrapper reads stdin → tempfile → calls `minimize_unsat_core_trace.py --z3 <real_z3> --quiet`
4. Same pattern in `web_viewer/test_logic.js` (resolves paths from project root)

## Comparison Mode

`--compare-minimization` in eval CLI:
- Runs all entries twice (baseline + minimized)
- Diffs classifications → `changedResults`
- Computes `addedTimeMs`, `slowdownFactor`
- Runs test suite twice, diffs per-test pass/fail

## Test Annotations

`.dfy` test files use `//::: L<line> - <Status>` comments. `bug_` prefixed dirs use inverted logic (failure = expected).

## Terminal Note

Terminal output capture broken on this system. Redirect to `.cmd_out.txt` and read back:
```bash
some_command 2>&1 > /home/ricostynha/Desktop/ProofPulse/.cmd_out.txt
```

## Coverage Statuses

- `CovComplete` — directly contributes to core postcondition proof flow
- `CovTest` — verified/connected but not essential to final contract intent
- `Uncovered` — not used for meaningful proof contribution

Two layers: `CovStatusInternal` (raw graph-derived) → `CovStatus` (post-processed by token class policy). Auto assertions forced to covered. Manual assertions can be downgraded. Top postconditions use alias/parent checks.

## Known Limitations

1. Proof-text string matching sensitive to Dafny/Boogie output wording changes
2. Unsat core can remain non-minimal even with minimization options
3. Partially overlapping spans skipped for valid nested HTML
4. Raw dependency facts and policy interpretation are mixed
5. Cross-call and allocation traceability partially heuristic
6. `forall` quantifier attribution is weak (known issue)
7. Simple assignment coverage can misclassify (e.g. task 309 Max)

## Specs

Active specs in `.kiro/specs/`. Check `tasks.md` for implementation status. Optional tasks marked with `*`.
