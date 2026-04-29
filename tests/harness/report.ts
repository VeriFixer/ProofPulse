import { writeFile } from 'fs/promises';

// ── Types ──

export interface TestResult {
  srcFile: string;
  res: {
    status: string;
    reason?: string;
    test_name?: string;
  };
  isBug: boolean;
  duration: number;
  lineStatus: string[];
}

export interface TestSummary {
  total: number;
  passed: number;
  failed: number;
  skipped: number;
  dafnyFailures?: number;
  errors: number;
}

interface CoverageTest {
  name: string;
  file: string;
  status: string;
  duration: number;
  isBug: boolean;
  coverageDistribution: Record<string, number>;
}

interface CoverageJSON {
  summary: {
    total: number;
    passed: number;
    failed: number;
    skipped: number;
    errors: number;
    timestamp: string;
  };
  tests: CoverageTest[];
}

// ── XML helpers ──

/**
 * Escape special XML characters.
 */
export function escapeXml(str: string | undefined | null): string {
  if (!str) return '';
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&apos;');
}

// ── JUnit XML ──

/**
 * Build JUnit XML string from test results.
 */
export function buildJUnitXML(results: TestResult[]): string {
  const testCases = results.map(result => {
    const { srcFile, res, isBug, duration } = result;

    let effectiveStatus = res.status;
    let failureMessage = '';

    if (isBug) {
      if (res.status === 'failed') {
        effectiveStatus = 'passed';
      } else if (res.status === 'passed') {
        effectiveStatus = 'failed';
        failureMessage = 'unexpected pass for bug test';
      }
    }

    const relativePath = srcFile.replace(/^dataset\/tests\//, '');
    const classname = relativePath.replace(/\.dfy$/, '').replace(/\//g, '.');
    const testName = res.test_name || relativePath.replace(/.*\//, '').replace(/\.dfy$/, '');

    let testcase = `    <testcase name="${escapeXml(testName)}" classname="${escapeXml(classname)}" time="${duration.toFixed(3)}"`;

    if (effectiveStatus === 'failed') {
      testcase += `>\n`;
      if (failureMessage) {
        testcase += `      <failure message="${escapeXml(failureMessage)}">${escapeXml(res.reason)}</failure>\n`;
      } else if (res.reason) {
        testcase += `      <failure message="${escapeXml(res.reason)}">${escapeXml(res.reason)}</failure>\n`;
      } else {
        testcase += `      <failure message="Test failed"/>`;
      }
      testcase += `    </testcase>`;
    } else if (effectiveStatus === 'skipped') {
      testcase += `>\n`;
      testcase += `      <skipped message="${escapeXml(res.reason || '')}"/>`;
      testcase += `    </testcase>`;
    } else if (effectiveStatus === 'error') {
      testcase += `>\n`;
      testcase += `      <error message="${escapeXml(res.reason || 'error')}">${escapeXml(res.reason)}</error>\n`;
      testcase += `    </testcase>`;
    } else {
      testcase += `/>`;
    }

    return testcase;
  });

  const total = results.length;
  const failures = results.filter(r => {
    if (r.isBug) return r.res.status === 'passed';
    return r.res.status === 'failed';
  }).length;
  const skipped = results.filter(r => r.res.status === 'skipped').length;
  const errors = results.filter(r => r.res.status === 'error').length;
  const time = results.reduce((sum, r) => sum + r.duration, 0);

  const testsuite = `  <testsuite name="ProofPulse" tests="${total}" failures="${failures}" errors="${errors}" skipped="${skipped}" time="${time.toFixed(3)}">
${testCases.join('\n')}
  </testsuite>`;

  return `<?xml version="1.0" encoding="UTF-8"?>
<testsuites>
${testsuite}
</testsuites>`;
}

/**
 * Write JUnit XML report from test results.
 */
export async function writeJUnitXML(results: TestResult[], outputPath: string): Promise<void> {
  try {
    const xml = buildJUnitXML(results);
    await writeFile(outputPath, xml, 'utf8');
  } catch (err: unknown) {
    const msg = err instanceof Error ? err.message : String(err);
    console.error(`Failed to write JUnit XML to ${outputPath}: ${msg}`);
  }
}

// ── Coverage JSON ──

/**
 * Build coverage JSON object from test results.
 */
export function buildCoverageJSON(results: TestResult[], summary: TestSummary): CoverageJSON {
  const tests: CoverageTest[] = results.map(result => {
    const { srcFile, res, isBug, duration, lineStatus } = result;

    const coverageDistribution: Record<string, number> = {
      CovComplete: 0,
      CovTest: 0,
      Uncovered: 0,
    };

    if (lineStatus && Array.isArray(lineStatus)) {
      for (const status of lineStatus) {
        if (status in coverageDistribution) {
          coverageDistribution[status]++;
        }
      }
    }

    return {
      name: res.test_name || srcFile.replace(/.*\//, '').replace(/\.dfy$/, ''),
      file: srcFile,
      status: res.status,
      duration,
      isBug,
      coverageDistribution,
    };
  });

  return {
    summary: {
      total: summary.total,
      passed: summary.passed,
      failed: summary.failed,
      skipped: summary.skipped,
      errors: summary.errors,
      timestamp: new Date().toISOString(),
    },
    tests,
  };
}

/**
 * Write coverage JSON report.
 */
export async function writeCoverageJSON(
  results: TestResult[],
  summary: TestSummary,
  outputPath: string,
): Promise<void> {
  try {
    const coverage = buildCoverageJSON(results, summary);
    await writeFile(outputPath, JSON.stringify(coverage, null, 2), 'utf8');
  } catch (err: unknown) {
    const msg = err instanceof Error ? err.message : String(err);
    console.error(`Failed to write coverage JSON to ${outputPath}: ${msg}`);
  }
}

/**
 * Compute exit code from test results.
 * Exit 0 iff all effective results pass (with bug inversion).
 */
export function computeExitCode(results: Array<{ status: string; isBug: boolean }>): number {
  for (const { status, isBug } of results) {
    const effectivePass =
      (status === 'passed' && !isBug) ||
      (status === 'failed' && isBug) ||
      status === 'skipped';
    if (!effectivePass) return 1;
  }
  return 0;
}
