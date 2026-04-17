# ProofPulse

Dafny proof dependency and coverage analysis tool. Runs Dafny verification on `.dfy` files, compares coverage status against expected annotations, and visualises results in a static web viewer.

## Quick start (Docker — recommended)

No local Dafny install needed. Docker bundles Node.js 22 + Dafny CLI.

```bash
# Build
docker build -t proofpulse .

# Run tests
docker run --name pp-test proofpulse

# Extract reports
docker cp pp-test:/app/test-results ./test-results
docker rm pp-test
```

Analyse a local `.dfy` file via volume mount:

```bash
docker run -v /path/to/file.dfy:/app/input.dfy proofpulse \
  dafny verify /app/input.dfy --verification-coverage-report cov
```

## Local setup (without Docker)

Requires Node.js 22+ and Dafny CLI in `PATH`.

```bash
npm install
npm test
```

`npm test` runs the full test harness: discovers `.dfy` files under `dataset/tests`, verifies each with Dafny, compares coverage against inline annotations, then writes structured reports to `test-results/`.

Exit codes: `0` = all pass, `1` = test failure, `2` = fatal error (e.g. Dafny not found).

## npm scripts

| Script | What it does |
|---|---|
| `npm test` | Full Dafny test suite + JUnit XML & coverage JSON reports |
| `npm start` | Start the interactive coverage viewer server (port 8080) |
| `npm run test:unit` | Property-based + unit tests for the report module |
| `npm run test:server` | Unit tests for the backend server |
| `npm run test:property` | Property-based tests for backend API correctness |
| `npm run test:bundle` | Unit tests for the static viewer bundling script |

## Test reports

After `npm test` (or Docker run), find these in `test-results/`:

- `junit.xml` — JUnit XML with one `<testcase>` per `.dfy` file (parseable by CI tools)
- `coverage.json` — per-test coverage distribution (CovComplete/CovTest/Uncovered) + summary

Override output paths via env vars:

```bash
JUNIT_REPORT_PATH=reports/junit.xml COVERAGE_REPORT_PATH=reports/cov.json npm test
```

## CI pipeline

GitHub Actions (`.github/workflows/ci.yml`) runs on push/PR to `main`:

1. Builds the Docker image
2. Runs `npm test` inside the container
3. Extracts JUnit XML + coverage JSON
4. Uploads reports as artifacts
5. Publishes test results as PR annotations via `dorny/test-reporter`

Non-zero exit code fails the workflow — use as a required status check to gate merges.

## Web viewer

### Interactive mode (recommended)

The viewer now ships with a built-in Node.js server that provides a test browser sidebar and interactive Dafny analysis — no manual file copying needed.

```bash
npm start
# Open http://localhost:8080
```

Features:
- Three-column layout: sidebar, editor, detail panel
- **Browser mode** — lists all tests from `dataset/tests/`, click to load coverage
- **Interactive mode** — paste any Dafny code, click "Run Coverage" to analyse on the fly
- Backend runs `dafny verify` with coverage flags, returns results to the viewer
- Toggle between modes with the Browser / Interactive buttons

The server accepts a custom port and tests directory:

```js
// From code
import { startServer } from './src/server.js';
await startServer(3000, 'path/to/tests');
```

### Static setup (no server)

```bash
# 1. Copy your .dfy file
cp path/to/your_file.dfy src/source_code.dfy

# 2. Run Dafny verification
dafny verify src/source_code.dfy \
  --verification-coverage-report cov \
  --log-format text \
  --solver-option LOG_FILE=output.smt2 \
  --bprint output.bpl \
  --isolate-assertions \
  > src/prover_log.txt

# 3. Serve and open
cd src && python3 -m http.server 8000
# Open http://localhost:8000/index.html
```

### Bundle script (local)

Package the viewer + pre-computed analysis into a self-contained static directory:

```bash
./scripts/bundle-viewer.sh <dfy-file> <output-dir>
```

Example:

```bash
./scripts/bundle-viewer.sh dataset/tests/test_assert_cov_complete/test_assert_cov_complete.dfy dist/viewer

# Open the viewer
cd dist/viewer && python3 -m http.server 8000
# Then open http://localhost:8000/index.html
```

The script copies `index.html`, `app.js`, `styles.css`, `spans_provider.js`, the `.dfy` file (as `source_code.dfy`), and `prover_log.txt` from the same directory as the `.dfy` file.

### Bundle and view via Docker

You can run the bundle script and serve the viewer entirely from Docker — no local Dafny or Node needed:

```bash
# 1. Build the image (if not done already)
docker build -t proofpulse .

# 2. Bundle a test's viewer output to a local directory
docker run --rm -v "$(pwd)/dist:/out" proofpulse \
  bash -c './scripts/bundle-viewer.sh dataset/tests/test_assert_cov_complete/test_assert_cov_complete.dfy /out/viewer'

# 3. Serve locally and open
cd dist/viewer && python3 -m http.server 8000
# Open http://localhost:8000/index.html
```

Or serve directly from Docker:

```bash
docker run --rm -p 8000:8000 -v "$(pwd)/dist/viewer:/srv" python:3-alpine \
  python3 -m http.server 8000 --directory /srv
# Open http://localhost:8000/index.html
```

If either `source_code.dfy` or `prover_log.txt` can't be loaded at runtime, the viewer shows a descriptive error indicating which file is missing.

## Configuration

| Env var | Default | Description |
|---|---|---|
| `DAFNY_TIMEOUT_SEC` | `60` | Per-test Dafny verification timeout (seconds) |
| `CI` | — | When set, concurrency scales to `max(1, cpus - 1)` |
| `JUNIT_REPORT_PATH` | `test-results/junit.xml` | JUnit XML output path |
| `COVERAGE_REPORT_PATH` | `test-results/coverage.json` | Coverage JSON output path |

## Bug tests

Test directories prefixed with `bug_` use inverted pass/fail logic: Dafny verification failure = expected (pass), verification success = unexpected (fail). This is reflected correctly in both JUnit XML and coverage JSON reports.

## Project structure

```
├── src/
│   ├── cli.js              # Entry point (npm test)
│   ├── test_logic.js       # Test harness (discovers + runs .dfy tests)
│   ├── report.js           # JUnit XML + coverage JSON generation
│   ├── report.test.js      # Property-based + unit tests
│   ├── server.js            # Backend HTTP server (API + static files)
│   ├── server.test.js       # Server unit + integration tests
│   ├── server.property.test.js # Property-based tests (fast-check)
│   ├── app.js              # Web viewer logic
│   ├── index.html          # Web viewer page (three-column layout)
│   ├── styles.css           # Web viewer styles
│   └── spans_provider.js   # Coverage span parser
├── scripts/
│   ├── bundle-viewer.sh       # Static viewer bundler
│   └── bundle-viewer.test.js  # Bundle script tests
├── dataset/
│   ├── tests/              # .dfy test files with expected annotations
│   └── demo/               # Demo files for presentations
├── Dockerfile
├── .github/workflows/ci.yml
└── package.json
```

## Demos

- Small examples showcase: `dataset/demo/_USECASE_demo_showcase_small_examples.dfy`
- Bugs and limitations: `dataset/demo/_USECASE_demo_bugs_limitations.dfy`
- Verus-to-Dafny translation: `dataset/demo/_USECASE_verus_fib_pow_translation.dfy`
- Deep write-up bundle: `dataset/demo/test_fully_use_postcondition/`
- Demo index: [dataset/demo/README.md](dataset/demo/README.md)
