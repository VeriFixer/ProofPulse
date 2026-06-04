#!/usr/bin/env npx tsx
import { runAllTests } from './test_logic.js';
import { writeJUnitXML, writeCoverageJSON } from './report.js';
import { mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const JUNIT_PATH = process.env.JUNIT_REPORT_PATH || 'test-results/junit.xml';
const COV_PATH = process.env.COVERAGE_REPORT_PATH || 'test-results/coverage.json';

const args = process.argv.slice(2);

if (args.includes('--help') || args.includes('-h')) {
  console.log(`
ProofPulse Test Harness

Usage: npm test -- [options]

Options:
  --dafny-path <path>            Path to Dafny binary (default: dafny in PATH)
  --force-minimization           Enable unsat core minimization
  --no-abstract-interpretation   Disable Dafny's abstract interpretation pass
  --update-snapshots             Regenerate snapshot YAML in .dfy files
  -h, --help                     Show this help message

Environment variables:
  DAFNY_TIMEOUT_SEC              Per-file verification timeout (default: 60)
  CI                             Adjusts concurrency
  JUNIT_REPORT_PATH              JUnit XML output path (default: test-results/junit.xml)
  COVERAGE_REPORT_PATH           Coverage JSON output path (default: test-results/coverage.json)

Examples:
  npm test
  npm test -- --dafny-path /path/to/dafny --force-minimization
  npm test -- --no-abstract-interpretation
  npm test -- --update-snapshots
  npm test -- --help
`.trim());
  process.exit(0);
}

const forceMinimization = args.includes('--force-minimization');
const updateSnapshots = args.includes('--update-snapshots');
const noAbstractInterpretation = args.includes('--no-abstract-interpretation');

let dafnyPath: string | undefined;
const dafnyIdx = args.indexOf('--dafny-path');
if (dafnyIdx !== -1 && args[dafnyIdx + 1]) {
  dafnyPath = args[dafnyIdx + 1];
}

try {
  const result = await runAllTests({ forceMinimization, dafnyPath, updateSnapshots, noAbstractInterpretation });
  if (!result) process.exit(0);

  const { results, summary } = result;

  await mkdir(dirname(JUNIT_PATH), { recursive: true });
  await mkdir(dirname(COV_PATH), { recursive: true });

  await writeJUnitXML(results, JUNIT_PATH);
  await writeCoverageJSON(results, summary, COV_PATH);
} catch (err) {
  console.error('Fatal error:', err);
  process.exitCode = 2;
}
