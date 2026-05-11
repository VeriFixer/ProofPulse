# ProofPulse

Dafny proof dependency and coverage analysis tool. Parses prover logs into a proof dependency graph, computes coverage status, and visualises results in a web viewer or VSCode extension.

## Watch the video demo to know more:
[![Watch the demo](https://img.youtube.com/vi/S8Yzr2twzLs/0.jpg)](https://www.youtube.com/watch?v=8pO3NAodjoQ)

## Installation

Two installation paths are available. Docker is recommended for artifact reviewers as it avoids platform mismatches.

### Option A: Docker (recommended)

Everything pre-packaged: Node.js, Dafny 4.11, Z3, VS Code with ProofPulse and Dafny extensions.

#### Using the pre-built image

A ready-to-use Docker image is provided as a `.tar.gz` archive (e.g. in the artifact submission):

```bash
docker load -i proofpulse-dev.tar.gz
```

#### Building the image yourself

If the pre-built image is not available:

```bash
git clone --recursive <repo-url>
cd ProofPulse
docker build -f Dockerfile.devenv -t proofpulse-dev .
```

#### Exporting the image as a tar.gz

To generate a portable image archive (e.g. for artifact submission):

```bash
docker save proofpulse-dev | gzip > proofpulse-dev.tar.gz
```

#### Starting the environment

Start an interactive session:

```bash
docker run -it -p 8080:8080 --entrypoint bash proofpulse-dev
```

From inside the container, launch the browser-based VS Code:

```bash
code-server --bind-addr 0.0.0.0:8080 --auth none /home/coder/project
```

Then open `http://localhost:8080` in your browser. You get a full VS Code with:
- Dafny 4.11 + Z3 ready in PATH
- ProofPulse extension pre-installed
- Project fully built (core, web viewer, extension)

> **First launch:** A popup may appear asking to install Dafny 4.11 — accept it. The Dafny extension will download its latest dependencies and after that everything works.

All commands in the sections below (Demo Examples, Evaluation Benchmark, etc.) can be run directly in this shell session.

---

### Option B: Manual installation

#### Prerequisites

- Node.js (≥18)
- Dafny ≥ 4.0 (in PATH or via the official Dafny VS Code extension)

#### Clone with submodules

This repo uses git submodules (e.g. `dafny-synthesis`). Either clone recursively:

```sh
git clone --recursive <repo-url>
```

Or if already cloned, init submodules:

```sh
git submodule update --init --recursive
```

> **Without this, the evaluation benchmark will exit immediately** because the `dafny-synthesis/` folder won't exist.

#### Build from source

```sh
npm install
npm run build   # builds core + web viewer + VSCode extension
```

#### VSCode extension

```bash
npm run package --prefix vscode_extension
code --install-extension vscode_extension/proofpulse-vscode-0.1.0.vsix
```

Or via the UI: Extensions sidebar → `...` → "Install from VSIX..." → select the `.vsix` file. Reload VSCode after installing.

> For more information on the VSCode extension (features, configuration, dev mode), see [`vscode_extension/README.md`](vscode_extension/README.md).

---

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

Feel free to follow the demo video on the examples displayed on there.

#### With the VSCode extension

1. Open any `.dfy` file from `demo_examples/`
2. Right-click on any highlighted line (covTest or uncovered) → **"ProofPulse: Get Proof Report"** (opens web viewer)
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

To run the full evaluation (~15 minutes):

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all
```

This will create this file:
`./evaluation/results/benchmark-results-aggregate-tables.tex`
with the first table results used in the paper.

```bash
# With minimization
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all --force-core-minimization
```

This will create this file:
`./evaluation/results/benchmark-results-aggregate-tables.tex`
with the first table results used in the paper.

These matched the evaluation results shown in the paper tables.