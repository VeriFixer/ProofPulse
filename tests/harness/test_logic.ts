import os from 'os';
import path from 'path';
import fs from 'fs';
import { parseProof, runDafny as coreRunDafny } from '@proofpulse/core';

const fsp = fs.promises;

const DAFNY_TIMEOUT_SEC = parseInt(process.env.DAFNY_TIMEOUT_SEC ?? '', 10) || 60;

const CONCURRENCY = process.env.CI
  ? Math.max(1, os.cpus().length - 1)
  : os.cpus().length - 1;

const DEFAULT_TESTS_ROOT = path.join('dataset', 'tests');

// ── ANSI helpers ──

const BOLD  = '\x1b[1m';
const DIM   = '\x1b[2m';
const RESET = '\x1b[0m';
const GREEN = '\x1b[32m';
const RED   = '\x1b[31m';
const YELLOW = '\x1b[33m';
const CYAN  = '\x1b[36m';
const GRAY  = '\x1b[90m';

function icon(status: string): string {
  switch (status) {
    case 'passed': return `${GREEN}✓${RESET}`;
    case 'failed': return `${RED}✗${RESET}`;
    case 'skipped': return `${YELLOW}⊘${RESET}`;
    case 'error': return `${RED}⚠${RESET}`;
    default: return '?';
  }
}

function shortPath(filePath: string): string {
  return filePath.replace(/^dataset\/tests\//, '');
}

function elapsed(sec: number): string {
  if (sec < 1) return `${(sec * 1000).toFixed(0)}ms`;
  return `${sec.toFixed(1)}s`;
}

// ── Types ──

interface RunTestResult {
  srcFile: string;
  status: string;
  test_name?: string;
  reason?: string;
  lineStatus?: string[];
  checkedLines?: number;
  dafnyRes?: { ok: boolean; reason?: string };
  error?: unknown;
  parsedTest?: unknown;
  expected?: unknown;
}

export interface TestRunResult {
  srcFile: string;
  res: RunTestResult;
  isBug: boolean;
  duration: number;
  lineStatus: string[];
}

export interface TestSummary {
  total: number;
  passed: number;
  failed: number;
  skipped: number;
  dafnyFailures: number;
  errors: number;
}

export interface RunAllTestsResult {
  results: TestRunResult[];
  summary: TestSummary;
}

interface RunOptions {
  testsRoot?: string;
  concurrency?: number;
  forceMinimization?: boolean;
}

// ── Test parsing ──

function parseTest(testSource: string): [string, Map<string, string>] {
  const expectedLines = new Map<string, string>();
  let testName = '';

  const lineRegex = /^\/\/:::\s*L(\d+)\s*-\s*([A-Za-z.]+)/;
  const nameRegex = /^\/\/:::\s*Name\s*-\s*(.*)/;

  const lines = testSource.split(/\r?\n/);
  for (const raw of lines) {
    const lineMatch = raw.match(lineRegex);
    const nameMatch = raw.match(nameRegex);

    if (lineMatch) {
      expectedLines.set(lineMatch[1], lineMatch[2]);
    }
    if (nameMatch) {
      testName = nameMatch[1];
    }
  }
  return [testName, expectedLines];
}

function checkTest(
  name: string,
  expected: Map<string, string>,
  received: string[],
): [boolean, string] {
  let testPassed = true;
  let reason = '\n';

  if (expected.size < 1) {
    reason = `  Failed ${name} : expect comments are empty"`;
    testPassed = false;
  }

  for (const [lineNum, expectedStatus] of expected.entries()) {
    const lineIdx = Number(lineNum);
    if (lineIdx < 1 || lineIdx > received.length) {
      testPassed = false;
      reason += `  Line ${lineNum} out of bounds (received ${received.length} lines)\n`;
    }

    const actualStatus = received[lineIdx - 1];
    if (actualStatus !== expectedStatus) {
      testPassed = false;
      reason += `  Line ${lineNum}: expected '${expectedStatus}', got '${actualStatus}'\n`;
    }
  }

  if (testPassed) {
    reason += `  Passed ${name}`;
  }
  return [testPassed, reason];
}

// ── File discovery ──

function findDfyFiles(startDir: string): string[] {
  const out: string[] = [];

  function walk(dir: string): void {
    const items = fs.readdirSync(dir, { withFileTypes: true });
    for (const it of items) {
      const full = path.join(dir, it.name);
      if (it.isDirectory()) {
        walk(full);
      } else if (it.isFile() && full.toLowerCase().endsWith('.dfy')) {
        out.push(full);
      }
    }
  }
  walk(startDir);
  return out;
}

// ── Single test runner ──

async function runTest(srcFile: string, opts: RunOptions = {}): Promise<RunTestResult> {
  const dafnyRes = await coreRunDafny(srcFile, {
    timeoutSeconds: DAFNY_TIMEOUT_SEC,
    forceMinimization: opts.forceMinimization,
  });

  if (dafnyRes.timedOut) {
    return { srcFile, status: 'failed', reason: 'timeout' };
  }
  if (dafnyRes.error) {
    return { srcFile, status: 'skipped', reason: 'dafny_failed', dafnyRes: { ok: false, reason: dafnyRes.error } };
  }

  let src: string;
  try {
    src = await fsp.readFile(srcFile, 'utf8');
  } catch (err) {
    return { srcFile, status: 'error', reason: 'read_source_failed', error: err };
  }

  const log = dafnyRes.log ?? '';

  const proofTest = parseProof(src, log);

  let parsedTest: [string, Map<string, string>];
  try {
    parsedTest = parseTest(src);
  } catch (err) {
    return { srcFile, status: 'error', reason: 'parse_test_failed', error: err };
  }

  if (!Array.isArray(parsedTest) || parsedTest.length < 2) {
    return { srcFile, status: 'error', reason: 'parse_test_return_invalid', parsedTest };
  }

  const [testName, testExpectedOut] = parsedTest;
  if (!(testExpectedOut instanceof Map)) {
    return { srcFile, status: 'error', reason: 'expected_not_map', expected: testExpectedOut };
  }

  const lineStatus = (proofTest && proofTest.lineStatus) || [];
  const checkedLines = testExpectedOut.size;
  try {
    const [ok, reason] = checkTest(testName, testExpectedOut, lineStatus);
    return { srcFile, status: ok ? 'passed' : 'failed', test_name: testName, reason, lineStatus, checkedLines };
  } catch (err) {
    return { srcFile, status: 'error', reason: 'check_test_exception', error: err };
  }
}

// ── Utilities ──

function isDafnyAvailable(): boolean {
  const pathEnv = process.env.PATH || '';
  const dirs = pathEnv.split(path.delimiter);
  for (const dir of dirs) {
    const candidate = path.join(dir, 'dafny');
    try {
      fs.accessSync(candidate, fs.constants.X_OK);
      return true;
    } catch {
      // not found in this dir
    }
  }
  return false;
}

// ── Main entry ──

export async function runAllTests(opts: RunOptions = {}): Promise<RunAllTestsResult> {
  const testsRoot = opts.testsRoot || DEFAULT_TESTS_ROOT;
  const startTime = performance.now();

  console.log(`\n${BOLD}${CYAN}ProofPulse Test Runner${RESET}`);
  console.log(`${GRAY}${'─'.repeat(50)}${RESET}`);
  console.log(`${DIM}Tests root:${RESET}  ${testsRoot}`);
  console.log(`${DIM}Timeout:${RESET}     ${DAFNY_TIMEOUT_SEC}s per file`);

  if (!isDafnyAvailable()) {
    console.error(`\n${RED}✗ Dafny CLI not found in PATH${RESET}`);
    console.error(`  Install Dafny and ensure it is on your PATH.`);
    process.exitCode = 2;
    return {
      results: [],
      summary: { total: 0, passed: 0, failed: 0, skipped: 0, dafnyFailures: 0, errors: 0 },
    };
  }

  if (!fs.existsSync(testsRoot)) {
    console.error(`\n${RED}✗ Tests folder not found: ${testsRoot}${RESET}`);
    process.exitCode = 2;
    return {
      results: [],
      summary: { total: 0, passed: 0, failed: 0, skipped: 0, dafnyFailures: 0, errors: 0 },
    };
  }

  const dfyFiles = findDfyFiles(testsRoot);
  console.log(`${DIM}Files found:${RESET} ${dfyFiles.length} .dfy`);

  if (dfyFiles.length === 0) {
    console.log(`\n${YELLOW}No test files found.${RESET}`);
    return {
      results: [],
      summary: { total: 0, passed: 0, failed: 0, skipped: 0, dafnyFailures: 0, errors: 0 },
    };
  }

  const concurrency = opts.concurrency || CONCURRENCY;
  console.log(`${DIM}Concurrency:${RESET} ${concurrency} workers`);
  if (opts.forceMinimization) {
    console.log(`${DIM}Minimization:${RESET} ${CYAN}enabled${RESET}`);
  }
  console.log(`${GRAY}${'─'.repeat(50)}${RESET}\n`);

  const results: TestRunResult[] = [];
  let idx = 0;
  let completedCount = 0;

  const workers = new Array(Math.min(concurrency, dfyFiles.length)).fill(0).map(async () => {
    while (true) {
      const myIndex = idx++;
      if (myIndex >= dfyFiles.length) return;
      const srcFile = dfyFiles[myIndex];
      const short = shortPath(srcFile);

      const isBug = srcFile.includes('bug_');
      const testStart = performance.now();
      const res = await runTest(srcFile, { forceMinimization: opts.forceMinimization });
      const duration = (performance.now() - testStart) / 1000;

      if (res.reason === 'timeout') {
        res.status = 'failed';
      }

      // Determine effective status for display
      let effectiveStatus = res.status;
      if (isBug && res.status === 'failed') effectiveStatus = 'passed';
      else if (isBug && res.status === 'passed') effectiveStatus = 'failed';

      completedCount++;
      const progress = `${GRAY}[${String(completedCount).padStart(3)}/${dfyFiles.length}]${RESET}`;
      const bugTag = isBug ? ` ${YELLOW}(bug test)${RESET}` : '';
      const timeTag = `${GRAY}${elapsed(duration)}${RESET}`;
      const lineCount = res.checkedLines ?? 0;
      const propsTag = lineCount > 0 ? ` ${DIM}(${lineCount} lines verified)${RESET}` : '';

      console.log(`  ${progress} ${icon(effectiveStatus)} ${short}${bugTag}${propsTag} ${timeTag}`);

      if (
        res.status === 'error' ||
        (isBug && res.status === 'passed') ||
        (!isBug && res.status === 'failed')
      ) {
        const reason = res.reason || 'unknown';
        console.error(`         ${RED}└─ ${reason}${RESET}`);
      }

      results.push({ srcFile, res, isBug, duration, lineStatus: res.lineStatus || [] });
    }
  });

  await Promise.all(workers);

  // Aggregate
  let passed = 0;
  let failed = 0;
  let skipped = 0;
  let dafnyFailures = 0;
  let errors = 0;

  for (const { srcFile, res, isBug } of results) {
    if (!res) {
      errors += 1;
      console.error(`No result for ${srcFile}`);
      continue;
    }
    switch (res.status) {
      case 'passed':
        if (!isBug) passed += 1;
        else failed += 1;
        break;
      case 'failed':
        if (isBug) passed += 1;
        else failed += 1;
        break;
      case 'skipped':
        skipped += 1;
        if (res.reason === 'dafny_failed') dafnyFailures += 1;
        break;
      case 'error':
      default:
        errors += 1;
        break;
    }
  }

  const totalTime = (performance.now() - startTime) / 1000;

  console.log(`\n${GRAY}${'─'.repeat(50)}${RESET}`);
  console.log(`${BOLD}Results${RESET}  ${elapsed(totalTime)} total\n`);
  console.log(`  ${GREEN}✓ Passed:${RESET}  ${passed}`);
  if (failed > 0) console.log(`  ${RED}✗ Failed:${RESET}  ${failed}`);
  else console.log(`  ${DIM}✗ Failed:  ${failed}${RESET}`);
  if (skipped > 0) console.log(`  ${YELLOW}⊘ Skipped:${RESET} ${skipped}`);
  if (dafnyFailures > 0) console.log(`  ${YELLOW}  └─ Dafny failures: ${dafnyFailures}${RESET}`);
  if (errors > 0) console.log(`  ${RED}⚠ Errors:${RESET}  ${errors}`);
  console.log('');

  if (failed > 0 || dafnyFailures > 0 || errors > 0) {
    console.error(`${RED}${BOLD}FAIL${RESET} — some tests did not pass.\n`);
    process.exitCode = 1;
  } else {
    console.log(`${GREEN}${BOLD}PASS${RESET} — all tests succeeded.\n`);
    process.exitCode = 0;
  }

  return {
    results,
    summary: { total: dfyFiles.length, passed, failed, skipped, dafnyFailures, errors },
  };
}
