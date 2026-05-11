# ProofPulse

Dafny proof dependency and coverage analysis tool. Parses prover logs into a proof dependency graph, computes coverage status, and visualises results in a web viewer or VSCode extension.

**Video demo:** [video.mp4](https://youtube.com/watch?v=video.mp4)

## Installation

### Prerequisites

- Node.js (≥18)
- Dafny (in PATH or via the official Dafny VS Code extension)

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
# Run in bash
npx tsx evaluation/src/cli.ts -h
```

To run the full evaluation:

```bash
# Run in bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all
```

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

## Testing

A comprehensive testing framework exists for ProofPulse. See [`CI_TESTING.md`](CI_TESTING.md) for full details on running unit tests, property tests, regression suites, and Docker-based testing.
