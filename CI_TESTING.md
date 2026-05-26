# CI & Testing

## Integration Tests (most critical)

These run the full pipeline: Dafny verification → log parsing → graph building → coverage → line status comparison against expected annotations in `.dfy` files under `dataset/tests/`.

Requires `dafny` in PATH.

```bash
# Run integration tests (dataset/tests/ annotation checks)
npm test

# With explicit dafny path
npm test -- --dafny-path /path/to/dafny

# With minimization enabled
npm test -- --force-minimization
```

## Full Pipeline Snapshot Tests

Snapshot tests use `snapshot_` prefixed folders in `dataset/tests/`. They run Dafny, build the proof graph, and compare the YAML output against `//::` comments embedded in the `.dfy` file itself.

```bash
# Run all tests (integration + snapshots together)
npm test

# Generate/update snapshot YAML in .dfy files
npm test -- --update-snapshots
```

### Adding a new snapshot test

1. Create `dataset/tests/snapshot_<name>/snapshot_<name>.dfy`
2. Add `//:: method MethodName:` at the end (empty = will be filled on update)
3. Run `npm test -- --update-snapshots` to generate the YAML into the file
4. Commit the `.dfy` file with the embedded `//::` YAML

### Format

The expected graph YAML is embedded directly in the `.dfy` file with `//::` prefix on each line:

```dafny
method Foo() { ... }

//:: method Foo:
//:: version: 1
//:: nodes:
//::   - id: ...
```

This keeps the expected output co-located with the source, same pattern as `//::: L<line> - <Status>` annotations for line-coverage tests.

---

## All Test Commands

```bash
npm test                        # Integration + snapshot tests (dataset/tests/)
npm test -- --update-snapshots  # Same but regenerates snapshot YAML in .dfy files
npm run test:all                # Run ALL test suites
npm run test:integration        # Same as npm test
npm run test:unit               # Unit tests (vitest)
npm run test:property           # Property-based tests (vitest + fast-check)
```

### Core module tests (unit + property)

```bash
cd core
npx vitest --run
```

## Testing with Docker

The Docker image includes Dafny and all dependencies — no local setup required.

```bash
docker build -t proofpulse .
docker run --rm proofpulse                       # Full test suite
docker run --rm proofpulse npm test              # Integration + snapshot tests
docker run --rm proofpulse npm run test:unit     # Unit tests only
```

## Test Infrastructure

The test harness (`tests/harness/`) discovers `.dfy` files under `dataset/tests/`, runs Dafny verification, parses the prover log with `@proofpulse/core`, and compares per-line coverage against `//::: L<line> - <Status>` annotations in the source.

Each test runs in its own temp dir — all artifacts are cleaned up automatically.

Reports are written to `test-results/junit.xml` and `test-results/coverage.json`.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `DAFNY_TIMEOUT_SEC` | `60` | Per-file verification timeout |
| `CI` | — | Adjusts concurrency |
| `JUNIT_REPORT_PATH` | `test-results/junit.xml` | JUnit XML output |
| `COVERAGE_REPORT_PATH` | `test-results/coverage.json` | Coverage JSON output |

## CLI Arguments (test harness)

| Argument | Description |
|----------|-------------|
| `--dafny-path <path>` | Explicit path to Dafny binary |
| `--force-minimization` | Enable unsat core minimization |

## Bug Tests

Directories prefixed with `bug_` use inverted logic — verification failure is the expected (passing) outcome.
