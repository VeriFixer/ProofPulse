# ProofPulse

Dafny proof dependency and coverage analysis tool. Parses prover logs into a proof dependency graph, computes coverage status, and visualises results in a web viewer or VSCode extension.

## Build

```bash
npm install
npm run build   # builds core + web viewer + VSCode extension
```

This single command compiles the core TypeScript library, bundles the browser viewer, and builds the VSCode extension. All components share `@proofpulse/core`.

## VSCode extension

### Install

```bash
npm run package --prefix vscode_extension
code --install-extension vscode_extension/proofpulse-vscode-0.1.0.vsix
```

Or via the UI: Extensions sidebar → `...` → "Install from VSIX..." → select the `.vsix` file. Reload VSCode after installing.

### Features

- Gutter decorations — red for uncovered lines, blue for CovTest
- Inline decorations — per-token coverage coloring
- Hover diagnostics — status, proof text, type, and dependency nodes
- Command palette: "ProofPulse: Run Coverage Analysis"
- Context menu: right-click a `.dfy` file → **"ProofPulse: Get Proof Report"** (opens web viewer)

### Configuration

| Setting | Default | Description |
|---|---|---|
| `proofpulse.dafnyPath` | `"dafny"` | Path to the Dafny executable. ProofPulse checks PATH first, then the official Dafny VS Code extension bundle, and errors out if neither is available |

| `proofpulse.timeoutSeconds` | `60` | Verification timeout in seconds |
| `proofpulse.forceMinimization` | `false` | Route Z3 calls through unsat core minimization pipeline |

### Dev/debug mode

Press `F5` from the project root to launch a temporary VSCode window with the extension loaded from source.

## Web viewer

```bash
npm start -- --file path/to/file.dfy
# Opens http://localhost:8080
```

### Docker

```bash
docker build -t proofpulse .
docker run -p 8080:8080 -v /path/to/file.dfy:/app/input.dfy proofpulse \
  npm start -- --file /app/input.dfy
```

## Tests

```bash
npm run test:all        # Run ALL test suites with clear separation
npm test                # Dafny regression suite only (requires dafny in PATH or the official Dafny VS Code extension)
npm run test:unit       # Unit tests (vitest)
npm run test:property   # Property-based tests (vitest + fast-check)
npm test -w evaluation  # Evaluation benchmark tests
```

### Testing with Docker

The Docker image includes Dafny and all dependencies — no local setup required.

```bash
# Run the full test suite
docker build -t proofpulse .
docker run --rm proofpulse

# Run a specific test command
docker run --rm proofpulse npm run test:unit
docker run --rm proofpulse npm run test:property
docker run --rm proofpulse npm test              # Dafny regression only
```

### Test infrastructure

The test harness (`tests/harness/`) discovers `.dfy` files under `dataset/tests/`, runs Dafny verification in isolated temp directories, parses the prover log with `@proofpulse/core`, and compares per-line coverage against `//::: L<line> - <Status>` annotations in the source.

Each test runs in its own temp dir — all artifacts are cleaned up automatically. Nothing is written to the source tree.

Reports are written to `test-results/junit.xml` and `test-results/coverage.json`.

| Variable | Default | Description |
|---|---|---|
| `DAFNY_TIMEOUT_SEC` | `60` | Per-file verification timeout |
| `CI` | — | Adjusts concurrency |
| `JUNIT_REPORT_PATH` | `test-results/junit.xml` | JUnit XML output |
| `COVERAGE_REPORT_PATH` | `test-results/coverage.json` | Coverage JSON output |

Directories prefixed with `bug_` use inverted logic — verification failure is the expected (passing) outcome.

## Core library (`@proofpulse/core`)

Shared TypeScript library used by both the VSCode extension and the web viewer.

- `parseProof(dafnyCode, proofLog)` → `Proof` with `ProofGraph` + `lineStatus`
- `runDafny(filePath, options?)` → `DafnyResult`
- `computeLineStatus(graph, sourceCode)` → per-line coverage
- `serializeProofGraph` / `deserializeProofGraph` — JSON round-trip
- Types: `CovStatus`, `TokenType`, `Node`, `ProofGraph`, `Proof`, `DafnyResult`

### Z3 Core Minimization

When `forceMinimization` is enabled, Z3 calls are routed through a Node.js wrapper that intercepts check-sat/get-unsat-core sequences and iteratively minimizes unsat cores for more precise proof dependency attribution.

```ts
import { runDafny } from "@proofpulse/core";
const result = await runDafny("file.dfy", { forceMinimization: true });
```

No external dependencies required — the minimization pipeline is pure TypeScript. Z3 is resolved from PATH first, then the official Dafny VS Code extension bundle.

## Evaluation Benchmark

Classifies dafny-synthesis specs as strong/weak using ProofPulse coverage, then compares against the paper's manual oracle.

```bash
# Full benchmark
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all

# Paper table (oracle only, no Dafny needed)
npx tsx evaluation/src/paper-table.ts --repo-root dafny-synthesis

# Comparison mode (baseline vs minimized)
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --compare-minimization
```

| Flag | Default | Description |
|---|---|---|
| `--repo-root <path>` | `dafny-synthesis` | Path to dafny-synthesis repo |
| `--dafny-path <path>` | `dafny` | Dafny binary |
| `--timeout <seconds>` | `60` | Per-file verification timeout |
| `--output <path>` | `benchmark-results.json` | JSON results output |
| `--dataset <id>` | `RQ3-GPT4` | Dataset: RQ1-GPT4, RQ1-PaLM2, RQ2-GPT4, RQ2-PaLM2, RQ3-GPT4, RQ3-PaLM2, or `all` |
| `--concurrency <n>` | cpus-1 | Parallel Dafny workers |
| `--verbose` | off | Print per-file details (forces sequential) |
| `--force-core-minimization` | off | Enable unsat core minimization |
| `--compare-minimization` | off | Run twice (baseline vs minimized), report diffs |


## Demos

- Small examples: `dataset/demo/_USECASE_demo_showcase_small_examples.dfy`
- Bugs and limitations: `dataset/demo/_USECASE_demo_bugs_limitations.dfy`
- Demo index: [dataset/demo/README.md](dataset/demo/README.md)


## WILL HAVE TO REDO THE LOGIC 


Simple Case:
Post 
  l 1
  l 2
  A 3
  Pre 1 

A 3 
  l 6 
  l 7 
  l 8

Graph 
Post -> l 1
     -> l 2
     -> l 3
     -> A 3 -> l 6
            -> l 7
            -> l 8 
     -> Pre 1 


Calls case precondiiton 

Post
  l 1
  l 2
  l 3

Call Post (main line) (If this is automatic, and i consider the same as postcondiiotn rip)
  r 1 

Will have to rethink better this with all example complexity

O principal problema parece sser que apenas devia ver a coverage na direcao que desce do topo para baixo e nao andar com ligacoes intermedias 

It seems that i will have to subdivide assertions automatic in two types
Calls, and the rest. Calls will allow me to distinchuish these cases of pre/post condiiton only used on calls (directly and easy)

2 improvemnts
- BFS just down direction (this will catch some bugs for sure)
- In the vizualization i can also show in two parts divided the botton direction and the top one.
- 2 types of automtic assertions

