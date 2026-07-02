# ProofPulse Artifact Evaluation README

**Paper title:** TBD

**Paper link:** TBD

**Artifact badge(s):** Available, Reusable, Functional

## Getting Started

ProofPulse is a Dafny proof-dependency and coverage analysis tool. It parses prover logs, builds a proof graph, computes line-level coverage, and shows the result in a browser viewer or the VS Code extension.

### What is included

* `core/` shared TypeScript library for parsing, proof graphs, coverage, and Dafny execution
* `evaluation/` benchmark runner, oracle handling, and results generation
* `demo_examples/` small Dafny files for smoke testing and exploration
* `dataset/` benchmark and debugging inputs
* `web_viewer/` browser-based visualization
* `vscode_extension/` editor integration

### Requirements

* Docker is the recommended review path.
* If you do not use Docker, you need Node.js 18 or newer, Dafny 4.x, and Z3 for minimization.
* Linux is the primary target; x86-64 and ARM64 are supported.
* No GPU is required.
* Allow roughly 10 GB of disk space for the repository and build artifacts.

### Installation

#### Recommended: Docker

1. Load the provided image archive.

```bash
docker load -i proofpulse-dev.tar.gz
```

2. Start the container.

```bash
docker run -it -p 8080:8080 --entrypoint bash proofpulse-dev
```

Note: If the port 8080:8080 is already in use, try a different port like 8081:8080

### Smoke Test


Run a bundled demo file and confirm that ProofPulse produces a coverage report.

```bash
node core/dist/cli.js demo_examples/C_cylinder_volume.dfy --dafny-path dafny --log
```

Expected result:

* The command completes successfully.
* The output contains a coverage report with covered and uncovered elements.
* Dafny verification runs for the demo input.

## Step-by-Step Instructions

The artifact supports the following paper claims:

* ProofPulse can analyze Dafny proofs and expose proof coverage on real examples.
* ProofPulse can reproduce the benchmark evaluation over the `dafny-synthesis` datasets.
* Unsat-core minimization changes the resulting coverage attribution and evaluation counts.

This artifact is documented, consistent, complete, and exercisable, and it includes appropriate verification and validation evidence through the smoke test, demo workflow, and benchmark workflow. Those qualities satisfy ACM's Functional badge criteria, while the archival packaging and the surrounding documentation support the Available and Reusable badges as well.

### 1. Reproduce the demo behavior
Inside docker:
1. Launch the browser-based VS Code environment.

```bash
code-server --bind-addr 0.0.0.0:8080 --auth none /home/coder/project
```
2. Open `http://localhost:8080` in your browser.

Note: You may need to trust the workspace (lower-left corner) before the VS Code environment starts. An internet connection is required the first time, as the bundled ProofPulse extension follows the standard Dafny extension packaging and automatically downloads its binary release on first use, matching the behavior of the official Dafny extension.

3. Open one of the files under `demo_examples/`.

Now you can follow what is done on the video of the extension for the rest of the examples:
[![Watch the demo](https://img.youtube.com/vi/S8Yzr2twzLs/0.jpg)](https://www.youtube.com/watch?v=8pO3NAodjoQ)

Note: Figure 1 of the paper corresponds to demo_examples/C_cylinder_volume.dfy. Feel free to comment out line
```
var a := CylinderVolume(3.0,4.0);
```
To test the paper claim:
```txt
"Figure 1. If line 8 were commented out, the precondition would
instead be classified as Uncovered, since it would neither be
exercised by callers nor required to prove the postcondition"Figure 1. If line 8 were commented out, the precondition would
instead be classified as Uncovered, since it would neither be
exercised by callers nor required to prove the postcondition"
```

The precondition will be marked uncovered so red.

Note: Figure 3 of the paper corresponds to demo_examples/A_vacuous_proof.dfy

Following the video you can open the webUI by hovering any component and then click on: "Click to Generate Proof Coverage Report"

### 2. Reproduce the Tables

1. Run the benchmark.

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all --no-abstract-interpretation
```

2. Generate the paper-style results report.

```bash
npx tsx evaluation/generate-results-md.ts
```

3. Inspect `results.md` and confirm that it contains the per-category precision, recall, and accuracy numbers on top.
```bash
head -n 12 results.md
```
Should produce results:
```txt
| Category | TP | FP | FN | TN | P | R | Acc |
|----------|----|----|----|----|------|------|------|
| Postconditions | 184 | 24 | 0 | 11 | 0.88 | 1.00 | 0.89 |
| Preconditions | 63 | 3 | 7 | 96 | 0.95 | 0.90 | 0.94 |
| Invariants | 77 | 13 | 0 | 11 | 0.86 | 1.00 | 0.87 |
```

These correspond to the values of Table 1, Cfg Base.

### 3. Reproduce the benchmark with minimization

1. Run the benchmark with unsat-core minimization enabled.

```bash
npx tsx evaluation/src/cli.ts --repo-root dafny-synthesis --dataset all --force-core-minimization --no-abstract-interpretation
```

2. Regenerate the report.

```bash
npx tsx evaluation/generate-results-md.ts
```

3. Inspect `results.md` and confirm that it contains the per-category precision, recall, and accuracy numbers on top.
```bash
head -n 12 results.md
```
Should produce results:
```txt
| Category | TP | FP | FN | TN | P | R | Acc |
|----------|----|----|----|----|------|------|------|
| Postconditions | 184 | 21 | 0 | 13 | 0.90 | 1.00 | 0.90 |
| Preconditions | 63 | 0 | 6 | 98 | 1.00 | 0.91 | 0.96 |
| Invariants | 77 | 10 | 0 | 13 | 0.89 | 1.00 | 0.90 |
```

These correspond to the values of Table 1, Cfg Min.

# Other notes

Feel free to see also the main README_main.md (that is the regular README of the project).
That has more informations on using and installing Proofpulse outside docker.