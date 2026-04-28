# ProofPulse

Dafny proof dependency and coverage analysis tool. Parses prover logs into a proof dependency graph, computes coverage status, and visualises results in a web viewer or VSCode extension.

## Quick start (Docker)

```bash
docker build -t proofpulse .
```
### Web viewer

Analyse a `.dfy` file and view the coverage graph in the browser:

```bash
docker run -p 8080:8080 -v /path/to/file.dfy:/app/input.dfy proofpulse \
  npm start -- --file /app/input.dfy
# Open http://localhost:8080
```

Example with a particular file inside image
/app/dataset/demo/_USECASE_demo_showcase_small_examples.dfy  

Or locally (without Docker):

```bash
node web_viewer/server.js --file path/to/file.dfy
# Opens browser at http://localhost:8080 with coverage graph
```

The viewer displays the editor and proof dependency panel for the given file.


### Run tests

```bash
# All CLI tests
npm test

# Unit tests
npm run test:unit

# Property-based tests (vitest)
npm run test:property

# Docker
docker run --name pp-test proofpulse

# Extract reports
docker cp pp-test:/app/test-results ./test-results
docker rm pp-test
```

## VSCode extension

Inline coverage analysis for `.dfy` files directly in the editor.

### Features

- Gutter decorations — red for uncovered lines, blue for CovTest
- Inline decorations — per-token coverage coloring
- Hover diagnostics — status, proof text, type, and all related dependency nodes
- Command palette: "ProofPulse: Run Coverage Analysis"
- Context menu: right-click a `.dfy` file → **"ProofPulse: Get Proof Report"**
  - Available in the editor context menu and the explorer context menu
  - Launches the web viewer for the selected file and opens it in the browser

### Configuration

| Setting | Default | Description |
|---|---|---|
| `proofpulse.dafnyPath` | `"dafny"` | Path to the Dafny executable |
| `proofpulse.timeoutSeconds` | `60` | Verification timeout in seconds |
| `proofpulse.forceMinimization` | `false` | Route Z3 calls through unsat core minimization pipeline |

### Building and installing

```bash
npm install
npm run build:core
cd vscode_extension && npm run build
```

#### Install as a `.vsix` (recommended for real usage)

Package the extension into a standard `.vsix` file, then install it like any other extension:

```bash
# Package (produces vscode_enowxtension/proofpulse-vscode-0.1.0.vsix)
cd vscode_extension && npm run package

# Install from the command line
code --install-extension vscode_extension/proofpulse-vscode-0.1.0.vsix
```

You can also install via the UI: open VSCode → Extensions sidebar → `...` menu → "Install from VSIX..." → select the `.vsix` file.

After installing, reload VSCode. The extension is now permanently available — no Extension Development Host needed.

To uninstall: Extensions sidebar → find ProofPulse → Uninstall.

#### Dev/debug mode (Extension Development Host)

For development iteration, press `F5` from the project root. This launches a temporary VSCode window with the extension loaded from source.

## Web server configuration

The HTTP server (`web_viewer/server.js`) accepts a `--file` argument:

```bash
node web_viewer/server.js --file path/to/file.dfy
```

| Env var | Default | Description |
|---|---|---|
| `DAFNY_TIMEOUT_SEC` | `60` | Dafny verification timeout (seconds) |
| `CI` | — | When set, concurrency scales to `max(1, cpus - 1)` |
| `JUNIT_REPORT_PATH` | `test-results/junit.xml` | JUnit XML output path |
| `COVERAGE_REPORT_PATH` | `test-results/coverage.json` | Coverage JSON output path |

## Build commands

| Command | Description |
|---|---|
| `npm run build:core` | Compile core TypeScript library |
| `npm run build:viewer` | Bundle spans provider for web viewer |
| `npm run build` | Build all (core + viewer) |
| `npm start -- --file path.dfy` | Start web viewer for a file |
| `npm test` | Run CLI tests |
| `npm run test:unit` | Run unit tests |
| `npm run test:property` | Run property-based tests (vitest) |

## Test reports

After `docker run` (or `npm test`), find in `test-results/`:

- `junit.xml` — one `<testcase>` per `.dfy` file
- `coverage.json` — per-test coverage distribution + summary

## CI pipeline

GitHub Actions (`.github/workflows/ci.yml`) on push/PR to `main`:

1. Builds Docker image
2. Runs `npm test`
3. Extracts JUnit XML + coverage JSON
4. Uploads reports as artifacts
5. Publishes test results via `dorny/test-reporter`

## Bug tests

Test directories prefixed with `bug_` use inverted pass/fail logic: verification failure = expected (pass), verification success = unexpected (fail).

## Core library (`@proofpulse/core`)

Shared TypeScript library used by both the VSCode extension and the web server.

- `parseProof(dafnyCode, proofLog)` — parse prover log into `Proof` with `ProofGraph` and `lineStatus`
- `runDafny(filePath, options?)` — spawn Dafny verification, return prover log
- `computeLineStatus(graph, sourceCode)` — per-line worst-case coverage
- `getNodesByLine`, `getRelatedNodes`, `getNodeInfo` — coverage queries
- `serializeProofGraph` / `deserializeProofGraph` — canonical JSON round-trip
- Types: `CovStatus`, `TokenType`, `Node`, `ProofGraph`, `Proof`, `DafnyResult`

### Z3 Core Minimization

When `forceMinimization` is enabled, Dafny's Z3 solver calls are routed through `minimize_unsat_core_trace.py` via a shell wrapper. This reduces non-minimal unsat cores for more precise proof dependency attribution.

**Programmatic usage:**

```ts
import { runDafny } from "@proofpulse/core";

const result = await runDafny("file.dfy", {
  forceMinimization: true,
  timeoutSeconds: 120,
});
```

**How it works:** `runDafny` appends `/z3exe:<wrapper>` to Boogie args and sets `PROOFPULSE_Z3_PATH` + `PROOFPULSE_MINIMIZER_SCRIPT` env vars. The wrapper (`core/scripts/z3-minimizer-wrapper.sh`) intercepts SMT2 input and pipes it through the Python minimizer.

**Requirements:** `python3` and `z3` must be available in PATH.

## Project structure

```
├── core/                       # @proofpulse/core — shared TypeScript library
│   ├── src/
│   │   ├── types.ts
│   │   ├── node.ts
│   │   ├── proof-graph.ts
│   │   ├── proof.ts
│   │   ├── coverage.ts
│   │   ├── rendering.ts
│   │   ├── serialization.ts
│   │   ├── dafny-runner.ts
│   │   ├── browser-entry.ts    # Browser IIFE entry (builds spans_provider.js)
│   │   └── index.ts
│   ├── scripts/
│   │   ├── z3-minimizer-wrapper.sh
│   │   └── minimize_unsat_core_trace.py
│   ├── package.json
│   └── tsconfig.json
├── vscode_extension/           # VSCode extension (+ "Get Proof Report" context menu)
│   ├── src/
│   │   ├── extension.ts
│   │   ├── commands.ts
│   │   ├── decorations.ts
│   │   ├── hover.ts
│   │   └── config.ts
│   ├── esbuild.config.mjs
│   ├── package.json
│   └── tsconfig.json
├── web_viewer/                 # HTTP server + coverage graph viewer
│   ├── server.js               # HTTP server (--file <path.dfy>)
│   ├── app.js                  # Web viewer logic
│   ├── index.html              # Web viewer page
│   ├── styles.css
│   ├── spans_provider.js       # Built from core (npm run build:viewer)
│   ├── build-spans-provider.mjs # Bundles core → browser IIFE
│   ├── cli.js                  # Test harness entry point
│   ├── test_logic.js           # Test runner (supports forceMinimization)
│   └── report.js               # JUnit XML + coverage JSON
├── evaluation/                 # Benchmark CLI (comparison mode, classification)
├── tests/                      # All tests
│   ├── unit/                   # Unit tests (node:test / vitest)
│   ├── property/               # Property-based tests (vitest + fast-check)
│   ├── integration/            # Integration tests
│   └── test_data/              # Sample .dfy and .smt2 files
├── docs/                       # Project documentation
├── dataset/
│   ├── tests/                  # .dfy test files
│   └── demo/                   # Demo files
├── Dockerfile
└── package.json                # Root workspace (workspaces: ["core", "vscode_extension", "evaluation"])
```

## Evaluation Benchmark

Automated benchmark that classifies dafny-synthesis specs as strong/weak using ProofPulse coverage, then compares against the paper's manual oracle.

### Setup

```bash
# Clone the dafny-synthesis dataset (if not already a submodule)
git clone https://github.com/Mondego/dafny-synthesis.git

# Install dependencies
npm install
npm run build:core
```

### Run benchmark

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all
```

### Options

| Flag | Default | Description |
|---|---|---|
| `--repo-root <path>` | `dafny-synthesis` | Path to dafny-synthesis repo |
| `--dafny-path <path>` | `dafny` | Dafny binary |
| `--timeout <seconds>` | `60` | Per-file verification timeout |
| `--output <path>` | `benchmark-results.json` | JSON results output |
| `--dataset <id>` | `RQ3-GPT4` | Dataset: RQ1-GPT4, RQ1-PaLM2, RQ2-GPT4, RQ2-PaLM2, RQ3-GPT4, RQ3-PaLM2, or `all` |
| `--concurrency <n>` | cpus-1 | Number of parallel Dafny workers (disabled with --verbose) |
| `--interactive` | off | Step-by-step mode with keypress pause |
| `--verbose` | off | Print source code, coverage, and oracle for each file (forces sequential) |
| `--force-core-minimization` | off | Route Z3 calls through unsat core minimization pipeline |
| `--compare-minimization` | off | Run each entry twice (baseline vs minimized), report differences |

### Reproduce paper table (oracle only, no Dafny needed)

```bash
npx tsx evaluation/src/paper-table.ts --repo-root dafny-synthesis
```

### Comparison mode

Runs every entry twice (with and without minimization) and reports:
- `changedResults` — entries where classification differs
- `addedTimeMs` — total time added by minimization
- `slowdownFactor` — minimized total / baseline total
- Per-test pass/fail diffs from the test suite

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --compare-minimization
```

Results written to `benchmark-results-comparison.json` alongside the normal output.

### Run on all datasets

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all
```

### Run tests

```bash
npm test -w evaluation
```

### Output

Produces a confusion matrix (strong/weak predicted vs oracle) with precision, recall, F1, and accuracy. Results are also written to the JSON output file.

## Demos

- Small examples: `dataset/demo/_USECASE_demo_showcase_small_examples.dfy`
- Bugs and limitations: `dataset/demo/_USECASE_demo_bugs_limitations.dfy`
- Verus-to-Dafny translation: `dataset/demo/_USECASE_verus_fib_pow_translation.dfy`
- Deep write-up: `dataset/demo/test_fully_use_postcondition/`
- Demo index: [dataset/demo/README.md](dataset/demo/README.md)
