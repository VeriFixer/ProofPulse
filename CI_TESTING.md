# CI & Testing

## Test Commands

```bash
npm run test:all        # Run ALL test suites with clear separation
npm test                # Dafny regression suite only (requires dafny in PATH or the official Dafny VS Code extension)
npm run test:unit       # Unit tests (vitest)
npm run test:property   # Property-based tests (vitest + fast-check)
npm test -w evaluation  # Evaluation benchmark tests
```

## Testing with Docker

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

## Test Infrastructure

The test harness (`tests/harness/`) discovers `.dfy` files under `dataset/tests/`, runs Dafny verification in isolated temp directories, parses the prover log with `@proofpulse/core`, and compares per-line coverage against `//::: L<line> - <Status>` annotations in the source.

Each test runs in its own temp dir — all artifacts are cleaned up automatically. Nothing is written to the source tree.

Reports are written to `test-results/junit.xml` and `test-results/coverage.json`.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `DAFNY_TIMEOUT_SEC` | `60` | Per-file verification timeout |
| `CI` | — | Adjusts concurrency |
| `JUNIT_REPORT_PATH` | `test-results/junit.xml` | JUnit XML output |
| `COVERAGE_REPORT_PATH` | `test-results/coverage.json` | Coverage JSON output |

## Bug Tests

Directories prefixed with `bug_` use inverted logic — verification failure is the expected (passing) outcome.
