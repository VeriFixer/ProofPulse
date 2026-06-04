import os from 'os';
import path from 'path';
import fs from 'fs';
import { parseProof, runDafny as coreRunDafny, DafnyReportParser, applyCoverage, resolveDafnyPathWithSource, resolveZ3PathWithSource, probeVersion } from '@proofpulse/core';
import YAML from 'js-yaml';

const fsp = fs.promises;

const DAFNY_TIMEOUT_SEC = parseInt(process.env.DAFNY_TIMEOUT_SEC ?? '', 10) || 60;

const CONCURRENCY = process.env.CONCURRENCY
  ? Math.max(1, parseInt(process.env.CONCURRENCY, 10))
  : Math.max(1, os.cpus().length - 1);

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
  dafnyPath?: string;
  updateSnapshots?: boolean;
  noAbstractInterpretation?: boolean;
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

function isSnapshotTest(srcFile: string): boolean {
  return srcFile.includes('snapshot_');
}

/**
 * Extract expected YAML from //:: comments in a .dfy file.
 */
function extractExpectedYAML(src: string): string | null {
  const lines = src.split('\n');
  let inSection = false;
  const yamlLines: string[] = [];

  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed.match(/^\/\/:: method .+:$/)) {
      inSection = true;
      continue;
    }
    if (inSection && trimmed.startsWith('//:: ')) {
      yamlLines.push(trimmed.slice(5));
    } else if (inSection && trimmed === '//::') {
      yamlLines.push('');
    } else if (inSection && !trimmed.startsWith('//::') && trimmed !== '') {
      break;
    }
  }

  return yamlLines.length > 0 ? yamlLines.join('\n') : null;
}

/**
 * Normalize a parsed snapshot object for order-independent comparison.
 * Sorts nodes by locationId and edge arrays by their key fields.
 * Strips non-deterministic fields (batchDuration) from topMeta.
 */
function normalizeSnapshot(obj: any): void {
  if (!obj) return;
  if (Array.isArray(obj.nodes)) {
    obj.nodes.sort((a: any, b: any) => (a.locationId ?? '').localeCompare(b.locationId ?? ''));
    for (const node of obj.nodes) {
      if (Array.isArray(node.prooftexts)) node.prooftexts.sort();
      // Strip non-deterministic timing data
      if (node.topMeta) {
        delete node.topMeta.batchDuration;
      }
    }
  }
  if (obj.edges) {
    if (Array.isArray(obj.edges.provedBy)) {
      obj.edges.provedBy.sort((a: any, b: any) => (a.top ?? '').localeCompare(b.top ?? ''));
      for (const e of obj.edges.provedBy) {
        if (Array.isArray(e.provers)) e.provers.sort();
      }
    }
    if (Array.isArray(obj.edges.proofUnused)) {
      obj.edges.proofUnused.sort((a: any, b: any) => (a.top ?? '').localeCompare(b.top ?? ''));
      for (const e of obj.edges.proofUnused) {
        if (Array.isArray(e.unused)) e.unused.sort();
      }
    }
    if (Array.isArray(obj.edges.connections)) {
      obj.edges.connections.sort((a: any, b: any) => (a.call ?? '').localeCompare(b.call ?? ''));
      for (const e of obj.edges.connections) {
        if (Array.isArray(e.targets)) e.targets.sort();
      }
    }
  }
}

/**
 * Run a snapshot test: build graph from Dafny log, compare YAML against
 * the //:: comments embedded in the .dfy file itself.
 *
 * Expected format in .dfy:
 *   //:: method MethodName:
 *   //:: version: 1
 *   //:: nodes:
 *   //::   - id: ...
 *
 * If --update-snapshots is passed and the section is empty or mismatches,
 * the .dfy file is rewritten with the actual YAML embedded.
 */
async function runSnapshotTest(srcFile: string, opts: RunOptions = {}): Promise<RunTestResult> {
  const dafnyRes = await coreRunDafny(srcFile, {
    dafnyPath: opts.dafnyPath,
    timeoutSeconds: DAFNY_TIMEOUT_SEC,
    forceMinimization: opts.forceMinimization,
    noAbstractInterpretation: opts.noAbstractInterpretation,
  });

  if (dafnyRes.timedOut) {
    return { srcFile, status: 'failed', reason: 'timeout' };
  }
  if (dafnyRes.error) {
    return { srcFile, status: 'skipped', reason: 'dafny_failed', dafnyRes: { ok: false, reason: dafnyRes.error } };
  }

  const log = dafnyRes.log ?? '';
  let src: string;
  try {
    src = await fsp.readFile(srcFile, 'utf8');
  } catch (err) {
    return { srcFile, status: 'error', reason: 'read_source_failed', error: err };
  }

  // Build graph
  const graph = DafnyReportParser.parseAndBuild(log);
  applyCoverage(graph);

  // Generate YAML, strip non-deterministic extras
  const rawYaml = graph.toYAML();
  const parsed = JSON.parse(JSON.stringify(YAML.load(rawYaml)));
  if (parsed && parsed.nodes) {
    for (const node of parsed.nodes) {
      delete node.extras;
      // batchDuration is timing data — non-deterministic across runs
      if (node.topMeta) {
        delete node.topMeta.batchDuration;
      }
    }
  }
  const actualYAML = YAML.dump(parsed);

  // Extract expected YAML from //:: comments in the file
  const expectedYAML = extractExpectedYAML(src);

  // If no expected YAML or empty section
  if (!expectedYAML || expectedYAML.trim().length === 0) {
    if (opts.updateSnapshots) {
      const updated = embedYAMLInDfy(src, actualYAML);
      await fsp.writeFile(srcFile, updated, 'utf8');
      return {
        srcFile,
        status: 'passed',
        test_name: path.basename(srcFile),
        reason: `  Snapshot written into .dfy file (${parsed?.nodes?.length ?? 0} nodes)`,
        checkedLines: parsed?.nodes?.length ?? 0,
      };
    }
    return {
      srcFile,
      status: 'failed',
      test_name: path.basename(srcFile),
      reason: `  No expected YAML in file. Run with --update-snapshots to generate.`,
      checkedLines: 0,
    };
  }

  // Compare structurally (YAML string formatting is non-deterministic)
  const expectedParsed = JSON.parse(JSON.stringify(YAML.load(expectedYAML)));

  // Normalize both sides: sort nodes by locationId, sort edge arrays
  normalizeSnapshot(parsed);
  normalizeSnapshot(expectedParsed);

  const actualJSON = JSON.stringify(parsed);
  const expectedJSON = JSON.stringify(expectedParsed);

  if (actualJSON === expectedJSON) {
    return {
      srcFile,
      status: 'passed',
      test_name: path.basename(srcFile),
      reason: `  Snapshot matches (${parsed?.nodes?.length ?? 0} nodes)`,
      checkedLines: parsed?.nodes?.length ?? 0,
    };
  }

  // Mismatch — count node-level diffs for reporting
  const actualNodes = parsed?.nodes?.length ?? 0;
  const expectedNodes = expectedParsed?.nodes?.length ?? 0;
  let diffSummary = `nodes: ${expectedNodes}→${actualNodes}`;
  if (actualNodes === expectedNodes && parsed?.nodes && expectedParsed?.nodes) {
    let nodeDiffs = 0;
    for (let i = 0; i < actualNodes; i++) {
      if (JSON.stringify(parsed.nodes[i]) !== JSON.stringify(expectedParsed.nodes[i])) nodeDiffs++;
    }
    diffSummary = `${nodeDiffs}/${actualNodes} nodes differ`;
  }

  if (opts.updateSnapshots) {
    const updated = embedYAMLInDfy(src, actualYAML);
    await fsp.writeFile(srcFile, updated, 'utf8');
    return {
      srcFile,
      status: 'passed',
      test_name: path.basename(srcFile),
      reason: `  Snapshot updated in .dfy file (${diffSummary})`,
      checkedLines: parsed?.nodes?.length ?? 0,
    };
  }

  return {
    srcFile,
    status: 'failed',
    test_name: path.basename(srcFile),
    reason: `  Snapshot mismatch (${diffSummary}). Update with: npm test -- --update-snapshots`,
    checkedLines: parsed?.nodes?.length ?? 0,
  };
}

/**
 * Rewrite the .dfy file: keep everything before the `//:: method` header,
 * then write the header + YAML with //:: prefix on each line.
 */
function embedYAMLInDfy(src: string, yaml: string): string {
  const lines = src.split('\n');
  // Find the //:: method header line
  let headerIdx = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim().match(/^\/\/:: method .+:$/)) {
      headerIdx = i;
      break;
    }
  }

  // Keep everything up to and including the header line
  const prefix = headerIdx >= 0
    ? lines.slice(0, headerIdx + 1)
    : [...lines, '//:: method Graph:'];

  // Embed YAML with //:: prefix
  const yamlLines = yaml.split('\n').map(l => l === '' ? '//::'  : `//:: ${l}`);

  return [...prefix, ...yamlLines, ''].join('\n');
}

async function runTest(srcFile: string, opts: RunOptions = {}): Promise<RunTestResult> {
  // Snapshot tests use graph YAML comparison
  if (isSnapshotTest(srcFile)) {
    return runSnapshotTest(srcFile, opts);
  }

  const dafnyRes = await coreRunDafny(srcFile, {
    dafnyPath: opts.dafnyPath,
    timeoutSeconds: DAFNY_TIMEOUT_SEC,
    forceMinimization: opts.forceMinimization,
    noAbstractInterpretation: opts.noAbstractInterpretation,
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

function isDafnyAvailable(dafnyPath?: string): boolean {
  // If explicit path provided, check that directly
  if (dafnyPath) {
    try {
      fs.accessSync(dafnyPath, fs.constants.X_OK);
      return true;
    } catch {
      return false;
    }
  }

  const pathEnv = process.env.PATH || '';
  const dirs = pathEnv.split(path.delimiter);
  const names = ['dafny', 'Dafny'];
  for (const dir of dirs) {
    for (const name of names) {
      const candidate = path.join(dir, name);
      try {
        fs.accessSync(candidate, fs.constants.X_OK);
        return true;
      } catch {
        // not found in this dir
      }
    }
  }
  return false;
}

// ── Main entry ──

function probeVersionShort(bin: string): string {
  const v = probeVersion(bin, '--version') ?? probeVersion(bin, '-version');
  if (!v) return 'unknown';
  const m = v.match(/(\d+\.\d+[\.\d]*)/);
  return m ? m[1] : v.split('\n')[0];
}

export async function runAllTests(opts: RunOptions = {}): Promise<RunAllTestsResult> {
  const testsRoot = opts.testsRoot || DEFAULT_TESTS_ROOT;
  const startTime = performance.now();

  const dafnyResolved = resolveDafnyPathWithSource(opts.dafnyPath ?? 'dafny');
  const dafnyBin = dafnyResolved?.path ?? opts.dafnyPath ?? 'dafny';
  const z3Resolved = dafnyResolved ? resolveZ3PathWithSource(dafnyBin) : undefined;
  const z3Bin = z3Resolved?.path ?? 'z3';
  const dafnyVersion = probeVersionShort(dafnyBin);
  const z3Version = probeVersionShort(z3Bin);

  console.log(`\n${BOLD}${CYAN}ProofPulse Test Runner${RESET}`);
  console.log(`${GRAY}${'─'.repeat(50)}${RESET}`);
  console.log(`${DIM}Tests root:${RESET}  ${testsRoot}`);
  console.log(`${DIM}Timeout:${RESET}     ${DAFNY_TIMEOUT_SEC}s per file`);
  console.log(`${DIM}Dafny:${RESET}       ${dafnyBin} ${GRAY}(${dafnyVersion})${RESET}`);
  console.log(`${DIM}Z3:${RESET}          ${z3Bin} ${GRAY}(${z3Version})${RESET}`);

  if (!isDafnyAvailable(opts.dafnyPath)) {
    console.error(`\n${RED}✗ Dafny CLI not found${opts.dafnyPath ? ` at ${opts.dafnyPath}` : ' in PATH'}${RESET}`);
    console.error(`  Install Dafny and ensure it is on your PATH, or pass --dafny-path <path>.`);
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

  let dfyFiles = findDfyFiles(testsRoot);

  // When updating snapshots, only run snapshot_ tests
  if (opts.updateSnapshots) {
    dfyFiles = dfyFiles.filter(f => f.includes('snapshot_'));
  }

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
  if (opts.noAbstractInterpretation) {
    console.log(`${DIM}Abstract interp:${RESET} ${CYAN}disabled${RESET}`);
  }
  if (opts.updateSnapshots) {
    console.log(`${DIM}Snapshots:${RESET}   ${CYAN}update mode${RESET}`);
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

      const isBug = srcFile.includes('bug_') && !srcFile.includes('snapshot_');
      const testStart = performance.now();
      const res = await runTest(srcFile, { forceMinimization: opts.forceMinimization, dafnyPath: opts.dafnyPath, updateSnapshots: opts.updateSnapshots, noAbstractInterpretation: opts.noAbstractInterpretation });
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
      const isSnapshot = srcFile.includes('snapshot_');
      const bugTag = isBug ? ` ${YELLOW}(bug test)${RESET}` : isSnapshot ? ` ${CYAN}(snapshot)${RESET}` : '';
      const timeTag = `${GRAY}${elapsed(duration)}${RESET}`;
      const lineCount = res.checkedLines ?? 0;
      const propsTag = lineCount > 0 ? ` ${DIM}(${lineCount} lines verified)${RESET}` : '';

      console.log(`  ${progress} ${icon(effectiveStatus)} ${short}${bugTag}${propsTag} ${timeTag}`);

      if (
        res.status === 'error' ||
        res.status === 'skipped' ||
        (isBug && res.status === 'passed') ||
        (!isBug && res.status === 'failed')
      ) {
        const reason = res.reason || 'unknown';
        console.error(`         ${RED}└─ ${reason}${RESET}`);
        if (res.dafnyRes && !res.dafnyRes.ok) {
          console.error(`         ${RED}   ${res.dafnyRes.reason}${RESET}`);
        }
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
