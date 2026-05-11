#!/usr/bin/env npx tsx
import { runAllTests } from './test_logic.js';
import { writeJUnitXML, writeCoverageJSON } from './report.js';
import { mkdir } from 'node:fs/promises';
import { dirname } from 'node:path';

const JUNIT_PATH = process.env.JUNIT_REPORT_PATH || 'test-results/junit.xml';
const COV_PATH = process.env.COVERAGE_REPORT_PATH || 'test-results/coverage.json';

const forceMinimization = process.argv.includes('--force-minimization');

try {
  const result = await runAllTests({ forceMinimization });
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
