# ProofPulse Artifact Evaluation README

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

#### Docker

> **Prerequisite:** Docker must be installed on your system. See the [official Docker installation guide](https://docs.docker.com/get-docker/) for instructions.

1. Load the provided image archive.

```bash
docker load -i proofpulse-dev.tar.gz
```

2. Start the container.

```bash
docker run -it -p 8080:8080 --entrypoint bash proofpulse-dev
```

Note: If port 8080:8080 is already in use, try a different host port like 8081:8080 (if you change the port, use the same one when opening localhost in your browser) (if you change the port you will have to use the same when opening on the localhost)

### Smoke Test

#### Cli Runs
Run a bundled demo file and confirm that ProofPulse produces a coverage report.

```bash
node core/dist/cli.js demo_examples/C_cylinder_volume.dfy --dafny-path dafny --log
```

Expected result:

* The command completes successfully.
* The output contains a coverage report 

Expected:
```txt
method CylinderVolume:
  - line: 3
    type: Precondition
    status: CovTest
    code: "requires radius >= 0.0 && height >= 0.0"
    message: "Precondition only used in calling tests, unnecessary to prove postconditions."
  - line: 4
    type: Postcondition
    status: CovTest
    code: "ensures volume >= 0.0"
    message: Postcondition not used in calling code — only in test assertions.

method main:
  - line: 10
    type: Call
    status: Uncovered
    code: "var a := CylinderVolume(3.0,4.0);"
    message: Not covered by any proof path.
```

#### VS code extension can run

Inside docker:
1. Launch the browser-based VS Code environment.

```bash
code-server --bind-addr 0.0.0.0:8080 --auth none /home/coder/project
```
2. Open `http://localhost:8080` in your browser. (or change by the port that was free for you instead of 8080 when lauching docker)

Note: A pop-up may appear in the browser-based VS Code asking you to trust the folder and allow the extensions to run. If ProofPulse does not start after accepting, you may need to enable the extension manually. Open the **Extensions** view in VS Code, search for **ProofPulse**, select it, and click **Enable**.

3. Open any of the files under  `demo_examples/` in the VS Code window in your browser. You will see both Dafny and ProofPulse running. ProofPulse colors lines based on their verification coverage status.

END OF SMOKE TEST

## Step-by-Step Instructions

The artifact supports the following paper claims:

* ProofPulse can analyze Dafny proofs and expose proof coverage on real examples.
* ProofPulse can reproduce the benchmark evaluation over the `dafny-synthesis` datasets.
* Unsat-core minimization changes the resulting coverage attribution and evaluation counts.

### 1. Reproduce the demo behavior

Inside docker:
1. Launch the browser-based VS Code environment.

```bash
code-server --bind-addr 0.0.0.0:8080 --auth none /home/coder/project
```
2. Open `http://localhost:8080` in your browser.

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

1. Run the benchmark. (5-15 minutes)

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

1. Run the benchmark with unsat-core minimization enabled. (5-15 minutes)

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

---

For usage and installation instructions outside Docker, see [README_main.md](README_main.md).
This concludes the paper reproducibility steps. The sections below provide additional context on the tool's architecture, extensibility, and validation infrastructure.

## Architecture and Extensibility

### Pipeline overview

ProofPulse follows a linear pipeline:

1. **Dafny execution** — `dafny-runner.ts` invokes Dafny with `--log-format text --isolate-assertions`, optionally routing Z3 through a minimizer wrapper.
2. **Log parsing** — `DafnyReportParser` consumes the structured text log and extracts assertion batches (top assertions, proof dependencies, unused clauses).
3. **Proof graph construction** — batches are converted to a `ProofGraph` (nodes = source spans, edges = provedBy / unused / call connections).
4. **Coverage computation** — two passes (`applyCoverageInternal` + `applyCoverageSemantic`) classify each node as `CovComplete`, `CovTest`, or `Uncovered`.
5. **Line-level status** — `computeLineStatus` aggregates node-level coverage into per-line colors for the editor and web viewer.

All of the above lives in `core/src/` and is shared between the CLI, the VS Code extension, and the browser viewer.

### Extensibility

* **Any Dafny program** can be analyzed — the tool operates on standard Dafny verification logs and requires no project-specific annotations.
* The source repository is publicly accessible: https://github.com/VeriFixer/ProofPulse
* **Other verification-aware languages**: the analysis logic is decoupled from Dafny internals. If another language (e.g., Boogie, SPARK, VeriFast) can produce a structured log with the same batch format (top assertion + proof dependencies + unused clauses), the rest of the pipeline would work without modification.

## Verification and Validation

ProofPulse ships with a dedicated validation test suite under `dataset/tests/`. Each subdirectory contains a `.dfy` file annotated with expected per-line coverage (e.g., `//::: L2 - CovComplete`) and, for snapshot tests, a full YAML serialization of the expected proof graph (embedded in `//::` comments).

### Exploring tests

Open any file from `dataset/tests/*` in VS Code with the Dafny and ProofPulse extensions installed to visually inspect its coverage output.

### Running all tests

```bash
npm test -- --force-minimization --no-abstract-interpretation 
```
Expected outcome:
```txt
ProofPulse Test Runner
──────────────────────────────────────────────────
Tests root:  dataset/tests
Timeout:     60s per file
Dafny:       /usr/local/bin/dafny (4.11.1)
Z3:          /usr/local/bin/z3 (4.12.1)
Files found: 71 .dfy
Concurrency: 15 workers 
Minimization: enabled
Abstract interp: disabled
──────────────────────────────────────────────────
(Followed by all test status and execution, like)
[ 60/71] ✓ test_post_cov_test/test_post_cov_test.dfy (4 lines verified) 8.5s
```
All tests are then run and should pass. On slower hardware, a test may occasionally fail due to timeouts, but this is unlikely as the suite passes consistently on GitHub CI. And the Concurrency depens on the actuall reviewer hardware (it picks the number of CPU cores of the machine).

### CI integration
Pushes to the main git repo are passed to a validation:

The same test command runs on every push and pull request via a GitHub Actions workflow (`.github/workflows/ci.yml`). The CI builds a Docker image from `Dockerfile.ci` with Dafny, Z3, and Node pre-installed, then executes the full test suite. Results are emitted as JUnit XML and a coverage JSON report under `test-results/`.
