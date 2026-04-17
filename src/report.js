import { writeFile } from 'fs/promises';

/**
 * Write JUnit XML report from test results
 * @param {Array} results - Array of test results from runAllTests
 * @param {string} outputPath - Path to write the JUnit XML file
 */
export async function writeJUnitXML(results, outputPath) {
  try {
    const xml = buildJUnitXML(results);
    await writeFile(outputPath, xml, 'utf8');
  } catch (err) {
    console.error(`Failed to write JUnit XML to ${outputPath}: ${err.message}`);
  }
}

/**
 * Build JUnit XML string from test results
 * @param {Array} results - Array of test results from runAllTests
 * @returns {string} JUnit XML string
 */
export function buildJUnitXML(results) {
  const testCases = results.map(result => {
    const { srcFile, res, isBug, duration } = result;
    
    // Determine effective status with bug test inversion
    let effectiveStatus = res.status;
    let failureMessage = '';
    
    if (isBug) {
      // Bug test: expected to fail, so invert the display
      if (res.status === 'failed') {
        effectiveStatus = 'passed';
      } else if (res.status === 'passed') {
        effectiveStatus = 'failed';
        failureMessage = 'unexpected pass for bug test';
      }
    }
    
    // Derive classname from file path (e.g., "dataset.tests.dir_name")
    const relativePath = srcFile.replace(/^dataset\/tests\//, '');
    const classname = relativePath.replace(/\.dfy$/, '').replace(/\//g, '.');
    
    // Extract test name from result or derive from file
    const testName = res.test_name || relativePath.replace(/.*\//, '').replace(/\.dfy$/, '');
    
    // Build testcase element
    let testcase = `    <testcase name="${escapeXml(testName)}" classname="${escapeXml(classname)}" time="${duration.toFixed(3)}"`;
    
    if (effectiveStatus === 'failed') {
      testcase += `>\n`;
      if (failureMessage) {
        testcase += `      <failure message="${escapeXml(failureMessage)}">${escapeXml(res.reason || '')}</failure>\n`;
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
      testcase += `      <error message="${escapeXml(res.reason || 'error')}">${escapeXml(res.reason || '')}</error>\n`;
      testcase += `    </testcase>`;
    } else {
      testcase += `/>`;
    }
    
    return testcase;
  });

  // Calculate totals
  const total = results.length;
  const failures = results.filter(r => {
    if (r.isBug) return r.res.status === 'passed'; // bug that passed is a failure
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
 * Escape special XML characters
 * @param {string} str - String to escape
 * @returns {string} Escaped string
 */
export function escapeXml(str) {
  if (!str) return '';
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&apos;');
}

/**
 * Write coverage JSON report
 * @param {Array} results - Array of test results from runAllTests
 * @param {Object} summary - Summary object from runAllTests
 * @param {string} outputPath - Path to write the coverage JSON file
 */
export async function writeCoverageJSON(results, summary, outputPath) {
  try {
    const coverage = buildCoverageJSON(results, summary);
    await writeFile(outputPath, JSON.stringify(coverage, null, 2), 'utf8');
  } catch (err) {
    console.error(`Failed to write coverage JSON to ${outputPath}: ${err.message}`);
  }
}

/**
 * Build coverage JSON object from test results
 * @param {Array} results - Array of test results from runAllTests
 * @param {Object} summary - Summary object from runAllTests
 * @returns {Object} Coverage JSON object
 */
export function buildCoverageJSON(results, summary) {
  const tests = results.map(result => {
    const { srcFile, res, isBug, duration, lineStatus } = result;
    
    // Calculate coverage distribution from lineStatus
    const coverageDistribution = {
      CovComplete: 0,
      CovTest: 0,
      Uncovered: 0
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
      duration: duration,
      isBug: isBug,
      coverageDistribution: coverageDistribution
    };
  });

  return {
    summary: {
      total: summary.total,
      passed: summary.passed,
      failed: summary.failed,
      skipped: summary.skipped,
      errors: summary.errors,
      timestamp: new Date().toISOString()
    },
    tests: tests
  };
}

/**
 * Compute exit code from test results.
 * Exit 0 iff all effective results pass (with bug inversion).
 * @param {Array<{status: string, isBug: boolean}>} results
 * @returns {number} 0 or 1
 */
export function computeExitCode(results) {
  for (const { status, isBug } of results) {
    // Effective pass: non-bug passed, or bug failed
    const effectivePass =
      (status === 'passed' && !isBug) ||
      (status === 'failed' && isBug) ||
      status === 'skipped';
    if (!effectivePass) return 1;
  }
  return 0;
}
