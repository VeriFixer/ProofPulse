# Agent Guide — ProofPulse

## Project Overview

ProofPulse analyzes Dafny verification proof logs to determine coverage of specifications (postconditions, preconditions, invariants). It parses prover output, builds proof graphs, propagates coverage, and classifies specs as "strong" or "weak".

## Workspace Structure

```
proofpulse/              # Root (npm workspaces)
├── core/                # @proofpulse/core — parser, proof graph, coverage, span-tree
│   └── src/             # TypeScript source (vitest for tests)
├── evaluation/          # @proofpulse/evaluation — classifier, benchmark-runner, oracle
│   └── src/
├── tests/               # Root-level test suites (unit, property, integration, harness)
│   ├── unit/
│   ├── property/
│   ├── integration/
│   ├── harness/         # Dafny regression harness (discovers .dfy files in dataset/tests/)
│   └── test_data/
├── dataset/             # Dafny test files + oracle labels
├── web_viewer/          # Browser-based proof visualization
├── vscode_extension/    # VS Code extension
└── docs/
```

## Key Commands

### Testing

| Command | What it does |
|---------|-------------|
| `npm run test:all` | ALL suites (unit + property + integration + server + bundle + evaluation + dafny regression) |
| `npm test` | Dafny regression suite only (requires `dafny` in PATH) |
| `npm run test:unit` | Unit tests via vitest (root config, `tests/unit/`) |
| `npm run test:property` | Property tests via vitest + fast-check (root config) |
| `npm test -w core` | Core workspace tests only (`core/src/__tests__/`) |
| `npm test -w evaluation` | Evaluation workspace tests only |

### With custom Dafny binary (local dev)

```bash
# Using --dafny-path (preferred)
npm test -- --dafny-path /home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny

# Or add to PATH (binary is capital-D "Dafny", resolver checks both cases)
PATH="/home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries:$PATH" npm test
```

### Building

```bash
npm run build:core    # TypeScript → dist/
npm run build         # core + viewer + extension
```

### Docker (no local Dafny needed)

```bash
docker build -t proofpulse .
docker run --rm proofpulse              # full suite
docker run --rm proofpulse npm test     # dafny regression only
```

## Architecture (core)

1. **Proof class** (`core/src/proof.ts`): Entry point. Two passes:
   - Pass 1 (`collectNodes`): Scans proof log, builds global spanMap for span promotion
   - Pass 2 (`buildGraph`): Creates per-family ProofGraph instances via FamilyGraphContainer
2. **FamilyGraphContainer** (`core/src/family-graph-container.ts`): Holds Map<familyKey, ProofGraph>. Family = (methodName, checkType) from "Results for X (Y)" headers.
3. **ProofGraph** (`core/src/proof-graph.ts`): Nodes + edges (provedBy/proves). Top assertions. BFS traversal.
4. **Coverage propagation** (`setCoverageStatusOnGraph`): BFS from postcondition tops, assigns CovStatus per node.
5. **Span-tree line status** (`core/src/span-tree.ts`): Containment tree per line, min over root spans.
6. **Classifier** (`evaluation/src/classifier.ts`): Uses composite status (max over families) to classify specs.

## Key Types

- `CovStatus`: `Uncovered | CovTest | CovComplete`
- `TokenType`: `Postcondition | Precondition | LoopInvariant | AssertionManual | AssertionAutomatic | CodeLine | Call`
- `FamilyId`: `{ methodName: string; checkType: string }`
- `Node`: Has `id` (span-based), `covStatus`, `covStatusInternal`, `type`, `isTopAssertion`, `scope`

## Test Expectations

- **Baseline**: 45/47 Dafny regression tests pass (2 known failures: `test_forall_needs_merging`, `test_visualizer_colapsing`)
- After per-family refactor: `test_forall_needs_merging` SHOULD now pass
- Core workspace: 69 tests (11 files)
- Property tests use `fast-check`

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `DAFNY_TIMEOUT_SEC` | `60` | Per-file verification timeout |
| `STRICT_SPAN_MERGE` | `0` | Set to `1` to throw on unmatched point nodes |
| `NODE_ENV` | — | `test` enables strict span merge |

## Bug Test Directories

Directories prefixed with `bug_` in `dataset/tests/` use inverted logic — verification failure is the expected (passing) outcome.

## Tips for Agents

- Always read existing code before editing. Match style.
- `core/src/index.ts` re-exports everything from core. Add exports there for new modules.
- The merged `proofGraph` on Proof class shares node objects with family graphs — mutations propagate.
- Classifier has overloads: `ProofGraph` (legacy) and `FamilyGraphContainer` (new).
- When running tests locally without Docker, ensure custom Dafny binary is in PATH.
