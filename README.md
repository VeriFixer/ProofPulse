# ProofPulse

This project analyzes Dafny proof dependencies and coverage.

## Prerequisites

- Node.js (tested with `v22`)
- Dafny CLI available in `PATH` (`dafny` command)

Optional (for the web viewer):
- Python 3 (for a quick local static server)

## Run all tests

From the repository root:

```bash
node src/test_logic.js
```

What this does:
- Recursively finds `.dfy` files under `dataset/tests`
- Runs Dafny verification per test file
- Compares produced coverage status against expected inline test annotations

If Dafny is not installed or not found in `PATH`, tests will be skipped with `dafny_failed`.

## Run the viewer for one specific file

The viewer expects these exact files inside `src`:
- `src/source_code.dfy`
- `src/prover_log.txt`

## Shared verification command

Use this exact command after the copy step:

```bash
dafny verify src/source_code.dfy \
  --verification-coverage-report cov \
  --log-format text \
  --solver-option LOG_FILE=output.smt2 \
  --bprint output.bpl \
  --isolate-assertions \
  > src/prover_log.txt
```

### 1) Put the target source file in place

Copy your Dafny file into:

```bash
cp path/to/your_file.dfy src/source_code.dfy
```

### 3) Start the web UI

Serve the `src` folder and open it in the browser:

```bash
cd src
python3 -m http.server 8000
```

## Demo and write-up references

- Demo bundle index: [dataset/demo/README.md](dataset/demo/README.md)
- Regular demo (small cases): [dataset/demo/_USECASE_demo_showcase_small_examples.dfy](dataset/demo/_USECASE_demo_showcase_small_examples.dfy)
- Bugs and limitations demo: [dataset/demo/_USECASE_demo_bugs_limitations.dfy](dataset/demo/_USECASE_demo_bugs_limitations.dfy)
- Verus-to-Dafny translation demo: [dataset/demo/_USECASE_verus_fib_pow_translation.dfy](dataset/demo/_USECASE_verus_fib_pow_translation.dfy)
- Deep write-up bundle (source, generated files, and write-up): [dataset/demo/test_fully_use_postcondition/](dataset/demo/test_fully_use_postcondition/)

Then open:

`http://localhost:8000/index.html`

The UI loads `app.js`, reads `source_code.dfy` and `prover_log.txt`, and shows dependency/coverage information.

## Ready-made demo file (multiple small cases)

For presentations, you can use:

- `dataset/demo/_USECASE_demo_showcase_small_examples.dfy`

It includes small examples for:
- A simple working case
- Redundant code lines
- No-contract case
- Specification lines not using code
- Irrelevant assertion

Quick run in the viewer:

```bash
cp dataset/demo/_USECASE_demo_showcase_small_examples.dfy src/source_code.dfy
```

Then run the shared verification command above and start the web UI.

## Ready-made demo file (bugs and limitations)

For a dedicated bugs/limitations presentation, use:

- `dataset/demo/_USECASE_demo_bugs_limitations.dfy`

This file groups:
- Known bug-style behaviors (unsat core non-minimality, call/assignment mapping)
- Known limitations (allocation traceability, no-contract signal, trivial specs)
- A compact "main difficulties" section for your demo narrative

Quick run in the viewer:

```bash
cp dataset/demo/_USECASE_demo_bugs_limitations.dfy src/source_code.dfy
```

Then run the shared verification command above and start the web UI.

## Ready-made demo file (Verus translation)

For a cross-language proof demo, use:

- `dataset/demo/_USECASE_verus_fib_pow_translation.dfy`

This file shows a Dafny translation of the Verus Fibonacci/power proof, including recursive specs, monotonicity lemmas, the bounded Fibonacci proof, and the runtime loop that mirrors the original proof structure.

Quick run in the viewer:

```bash
cp dataset/demo/_USECASE_verus_fib_pow_translation.dfy src/source_code.dfy
```

Then run the shared verification command above and start the web UI.