# ProofPulse

Dafny proof dependency and coverage analysis tool. Parses prover logs into a proof dependency graph, computes coverage status, and visualises results in a web viewer or VSCode extension.

## Watch the video demo to know more:
[![Watch the demo](https://img.youtube.com/vi/S8Yzr2twzLs/0.jpg)](https://www.youtube.com/watch?v=8pO3NAodjoQ)

## Installation

### Prerequisites

- Node.js (≥18)
- Dafny ≥ 4.0 (in PATH or via the official Dafny VS Code extension)

### Clone with submodules

This repo uses git submodules (e.g. `dafny-synthesis`). Either clone recursively:

```sh
git clone --recursive <repo-url>
```

Or if already cloned, init submodules:

```sh
git submodule update --init --recursive
```

> **Without this, the evaluation benchmark will exit immediately** because the `dafny-synthesis/` folder won't exist.

### Build from source

```sh
# Run in bash
npm install
npm run build   # builds core + web viewer + VSCode extension
```

### VSCode extension

```bash
# Run in bash
npm run package --prefix vscode_extension
code --install-extension vscode_extension/proofpulse-vscode-0.1.0.vsix
```

Or via the UI: Extensions sidebar → `...` → "Install from VSIX..." → select the `.vsix` file. Reload VSCode after installing.

> For more information on the VSCode extension (features, configuration, dev mode), see [`vscode_extension/README.md`](vscode_extension/README.md).

## Demo Examples

The `demo_examples/` folder contains sample Dafny files that showcase ProofPulse capabilities:

| File | Description |
|------|-------------|
| `A_vacuous_proof.dfy` | Vacuous proof detection |
| `B_demo.dfy` | General coverage demo |
| `C_cylinder_volume.dfy` | Numeric proof coverage |
| `D_core_minimization.dfy` | Unsat core minimization |
| `E_limitations.dfy` | Known limitations |

### Running the examples

#### With the VSCode extension

1. Open any `.dfy` file from `demo_examples/`
2. Right-click on any highlighted line (covTest or uncovered)→ **"ProofPulse: Get Proof Report"** (opens web viewer)
3. Or use Command Palette: "ProofPulse: Run Coverage Analysis" for gutter decorations


> **To see expected outputs for each example, see the [video demo](https://youtube.com/watch?v=video.mp4).**

## Core library (`@proofpulse/core`)

Shared TypeScript library used by both the VSCode extension and the web viewer.

- `parseProof(dafnyCode, proofLog)` → `Proof` with `ProofGraph` + `lineStatus`
- `runDafny(filePath, options?)` → `DafnyResult`
- `computeLineStatus(graph, sourceCode)` → per-line coverage
- `serializeProofGraph` / `deserializeProofGraph` — JSON round-trip
- Types: `CovStatus`, `TokenType`, `Node`, `ProofGraph`, `Proof`, `DafnyResult`

### Z3 Core Minimization

When `forceMinimization` is enabled, Z3 calls are routed through a Node.js wrapper that iteratively minimizes unsat cores for more precise proof dependency attribution.

## Evaluation Benchmark

Classifies dafny-synthesis specs as strong/weak using ProofPulse coverage, then compares against the paper's manual oracle.

```bash
# Run in bash to get evaluation options
npx tsx evaluation/src/cli.ts -h
```

To run the full evaluation:

```bash
# Run in bash to get evaluation without minimization
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all
```

This will create this file: 
ProofPulse/evaluation/results/benchmark-results-aggregate-tables.tex
With the first table results used on the paper.

```bash
# Run in bash to get evaluation with minimization
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all --force-core-minimization
```

This will create this file: 
ProofPulse/evaluation/results/benchmark-results-aggregate-tables.tex
With the first table results used on the paper.


These matched the Evaluation results shown on the paper tables.

| Flag | Default | Description |
|------|---------|-------------|
| `--repo-root <path>` | `dafny-synthesis` | Path to dafny-synthesis repo |
| `--dafny-path <path>` | `dafny` | Dafny binary |
| `--timeout <seconds>` | `60` | Per-file verification timeout |
| `--output <path>` | `benchmark-results.json` | JSON results output |
| `--dataset <id>` | `RQ3-GPT4` | Dataset: RQ1-GPT4, RQ1-PaLM2, RQ2-GPT4, RQ2-PaLM2, RQ3-GPT4, RQ3-PaLM2, or `all` |
| `--concurrency <n>` | cpus-1 | Parallel Dafny workers |
| `--verbose` | off | Print per-file details (forces sequential) |
| `--force-core-minimization` | off | Enable unsat core minimization |
| `--compare-minimization` | off | Run twice (baseline vs minimized), report diffs |

## Docker Development Environment

Run ProofPulse entirely in Docker with a browser-based VS Code — no local install of Node, Dafny, or extensions needed.

### Build the image

```bash
git clone --recursive <repo-url>
cd ProofPulse
docker build -f Dockerfile.devenv -t proofpulse-dev .
```

### Run

```bash
docker run -p 8080:8080 proofpulse-dev
```

Open `http://localhost:8080` in your browser. You get a full VS Code with:
- Dafny 4.11 + Z3 ready in PATH
- ProofPulse extension pre-installed
- Project fully built (core, web viewer, extension)

> **First launch:** A popup may appear asking to install Dafny 4.11 — accept it.

### Options

| Use case | Command |
|----------|---------|
| Password-protected | `docker run -p 8080:8080 -e PASSWORD=secret proofpulse-dev code-server --bind-addr 0.0.0.0:8080 --auth password /home/coder/project` |
| Mount local files | `docker run -p 8080:8080 -v $(pwd):/home/coder/project proofpulse-dev` |
| Run tests only (CI) | `docker build -t proofpulse-ci . && docker run proofpulse-ci` |

### Running the evaluation inside Docker

```bash
docker run proofpulse-dev bash -c "cd /home/coder/project && npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all"
```

## Testing

A comprehensive testing framework exists for ProofPulse. See [`CI_TESTING.md`](CI_TESTING.md) for full details on running unit tests, property tests, regression suites, and Docker-based testing.
