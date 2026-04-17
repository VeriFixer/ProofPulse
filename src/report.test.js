import { strict as assert } from 'node:assert';
import { test, describe } from 'node:test';
import fc from 'fast-check';
import {
  buildJUnitXML,
  buildCoverageJSON,
  writeJUnitXML,
  writeCoverageJSON,
  computeExitCode,
  escapeXml,
} from './report.js';

// ── Helpers ──

/** Minimal XML parser: extract testcase elements from JUnit XML */
function parseTestCases(xml) {
  const cases = [];
  // Single-pass: find each <testcase start, then determine if self-closing or has body
  const re = /<testcase\s+([^>]*?)(\/?>)/g;
  let m;
  while ((m = re.exec(xml)) !== null) {
    const attrs = m[1];
    const closing = m[2];
    let body = '';
    if (closing === '>') {
      // Find matching </testcase>
      const endIdx = xml.indexOf('</testcase>', re.lastIndex);
      if (endIdx !== -1) {
        body = xml.substring(re.lastIndex, endIdx);
        re.lastIndex = endIdx + '</testcase>'.length;
      }
    }

    const name = attr(attrs, 'name');
    const classname = attr(attrs, 'classname');
    const time = attr(attrs, 'time');

    let status = 'passed';
    let failureMessage = '';
    let failureText = '';
    const failMatch = /<failure\s+message="([^"]*)"[^>]*>([\s\S]*?)<\/failure>/.exec(body);
    const failSelf = /<failure\s+message="([^"]*)"[^/]*\/>/.exec(body);
    const errorMatch = /<error\s+message="([^"]*)"[^>]*>([\s\S]*?)<\/error>/.exec(body);
    const skipMatch = /<skipped/.exec(body);
    if (failMatch) {
      status = 'failed';
      failureMessage = unescapeXml(failMatch[1]);
      failureText = unescapeXml(failMatch[2]);
    } else if (failSelf) {
      status = 'failed';
      failureMessage = unescapeXml(failSelf[1]);
    } else if (errorMatch) {
      status = 'error';
      failureMessage = unescapeXml(errorMatch[1]);
      failureText = unescapeXml(errorMatch[2]);
    } else if (skipMatch) {
      status = 'skipped';
    }

    cases.push({ name: unescapeXml(name), classname, time: parseFloat(time), status, failureMessage, failureText });
  }
  return cases;
}

function attr(s, name) {
  const m = new RegExp(`${name}="([^"]*)"`).exec(s);
  return m ? m[1] : '';
}

function unescapeXml(s) {
  return s
    .replace(/&apos;/g, "'")
    .replace(/&quot;/g, '"')
    .replace(/&gt;/g, '>')
    .replace(/&lt;/g, '<')
    .replace(/&amp;/g, '&');
}

// ── Arbitraries ──

const statusArb = fc.constantFrom('passed', 'failed', 'skipped', 'error');
// Avoid XML-hostile chars in names/reasons to keep round-trip clean
const safeStringArb = fc.stringOf(fc.constantFrom(...'abcdefghijklmnopqrstuvwxyz0123456789_ '.split('')), { minLength: 1, maxLength: 30 });

const testResultArb = fc.record({
  srcFile: safeStringArb.map(s => `dataset/tests/${s.replace(/ /g, '_')}/${s.replace(/ /g, '_')}.dfy`),
  res: fc.record({
    status: statusArb,
    reason: fc.option(safeStringArb, { nil: undefined }),
    test_name: fc.option(safeStringArb, { nil: undefined }),
  }),
  isBug: fc.boolean(),
  duration: fc.double({ min: 0, max: 999, noNaN: true }),
  lineStatus: fc.array(fc.constantFrom('CovComplete', 'CovTest', 'Uncovered'), { minLength: 0, maxLength: 20 }),
});

const testResultsArb = fc.array(testResultArb, { minLength: 0, maxLength: 15 });

// ── Property 1: JUnit XML round-trip ──

describe('Feature: ci-spec-driven-development, Property 1: JUnit XML round-trip preserves test results', () => {
  test('round-trip: serialize then parse preserves count and statuses', () => {
    fc.assert(
      fc.property(testResultsArb, (results) => {
        const xml = buildJUnitXML(results);

        // Well-formed structure
        assert.ok(xml.includes('<?xml version="1.0"'));
        assert.ok(xml.includes('<testsuites>'));
        assert.ok(xml.includes('<testsuite '));
        assert.ok(xml.includes('</testsuites>'));

        const parsed = parseTestCases(xml);
        assert.equal(parsed.length, results.length, 'one testcase per result');

        for (let i = 0; i < results.length; i++) {
          const r = results[i];
          const p = parsed[i];

          // Expected effective status after bug inversion
          let expectedStatus = r.res.status;
          if (r.isBug && r.res.status === 'failed') expectedStatus = 'passed';
          if (r.isBug && r.res.status === 'passed') expectedStatus = 'failed';

          assert.equal(p.status, expectedStatus, `status mismatch at index ${i}`);

          // Bug test that passed → failure message about unexpected pass
          if (r.isBug && r.res.status === 'passed') {
            assert.ok(p.failureMessage.includes('unexpected pass'), `expected unexpected pass message at ${i}`);
          }
        }
      }),
      { numRuns: 100 }
    );
  });
});

// ── Property 2: Coverage JSON round-trip ──

describe('Feature: ci-spec-driven-development, Property 2: Coverage JSON round-trip preserves test data', () => {
  test('round-trip: serialize then parse preserves summary and coverage distribution', () => {
    fc.assert(
      fc.property(testResultsArb, (results) => {
        // Build a summary matching the test_logic.js aggregation
        let passed = 0, failed = 0, skipped = 0, errors = 0;
        for (const r of results) {
          switch (r.res.status) {
            case 'passed': r.isBug ? failed++ : passed++; break;
            case 'failed': r.isBug ? passed++ : failed++; break;
            case 'skipped': skipped++; break;
            default: errors++; break;
          }
        }
        const summary = { total: results.length, passed, failed, skipped, dafnyFailures: 0, errors };

        const json = buildCoverageJSON(results, summary);
        // Verify it round-trips through JSON.parse
        const reparsed = JSON.parse(JSON.stringify(json));

        assert.equal(reparsed.summary.total, summary.total);
        assert.equal(reparsed.summary.passed, summary.passed);
        assert.equal(reparsed.summary.failed, summary.failed);
        assert.equal(reparsed.summary.skipped, summary.skipped);
        assert.equal(reparsed.summary.errors, summary.errors);
        assert.ok(reparsed.summary.timestamp);

        assert.equal(reparsed.tests.length, results.length);

        for (let i = 0; i < results.length; i++) {
          const r = results[i];
          const t = reparsed.tests[i];

          assert.equal(t.status, r.res.status);
          assert.equal(t.isBug, r.isBug);

          // Verify coverage distribution matches lineStatus counts
          const expectedDist = { CovComplete: 0, CovTest: 0, Uncovered: 0 };
          for (const s of r.lineStatus || []) {
            if (s in expectedDist) expectedDist[s]++;
          }
          assert.deepStrictEqual(t.coverageDistribution, expectedDist);
        }
      }),
      { numRuns: 100 }
    );
  });
});

// ── Property 3: Exit code reflects test outcomes ──

describe('Feature: ci-spec-driven-development, Property 3: Exit code reflects test outcomes', () => {
  test('exit code is 0 iff all effective results pass', () => {
    const entryArb = fc.record({
      status: statusArb,
      isBug: fc.boolean(),
    });

    fc.assert(
      fc.property(fc.array(entryArb, { minLength: 0, maxLength: 20 }), (entries) => {
        const code = computeExitCode(entries);

        // Manually compute expected
        let allPass = true;
        for (const { status, isBug } of entries) {
          const effectivePass =
            (status === 'passed' && !isBug) ||
            (status === 'failed' && isBug) ||
            status === 'skipped';
          if (!effectivePass) { allPass = false; break; }
        }

        assert.equal(code, allPass ? 0 : 1);
      }),
      { numRuns: 100 }
    );
  });
});

// ── Unit tests: bug test inversion and error handling (Task 2.6) ──

describe('Bug test inversion in JUnit XML', () => {
  test('bug test with status "passed" → reported as failed with unexpected pass message', () => {
    const results = [{
      srcFile: 'dataset/tests/bug_example/bug_example.dfy',
      res: { status: 'passed', test_name: 'BugTest' },
      isBug: true,
      duration: 1.0,
      lineStatus: [],
    }];
    const xml = buildJUnitXML(results);
    const parsed = parseTestCases(xml);
    assert.equal(parsed.length, 1);
    assert.equal(parsed[0].status, 'failed');
    assert.ok(parsed[0].failureMessage.includes('unexpected pass'));
  });

  test('bug test with status "failed" → reported as passed', () => {
    const results = [{
      srcFile: 'dataset/tests/bug_example/bug_example.dfy',
      res: { status: 'failed', reason: 'verification failed', test_name: 'BugTest' },
      isBug: true,
      duration: 2.5,
      lineStatus: [],
    }];
    const xml = buildJUnitXML(results);
    const parsed = parseTestCases(xml);
    assert.equal(parsed.length, 1);
    assert.equal(parsed[0].status, 'passed');
  });
});

describe('Report write failure handling', () => {
  test('writeJUnitXML logs to stderr on write failure, does not throw', async () => {
    const stderrMessages = [];
    const origError = console.error;
    console.error = (...args) => stderrMessages.push(args.join(' '));
    try {
      // Write to an invalid path
      await writeJUnitXML([], '/nonexistent/dir/report.xml');
      assert.ok(stderrMessages.some(m => m.includes('Failed to write JUnit XML')));
    } finally {
      console.error = origError;
    }
  });

  test('writeCoverageJSON logs to stderr on write failure, does not throw', async () => {
    const stderrMessages = [];
    const origError = console.error;
    console.error = (...args) => stderrMessages.push(args.join(' '));
    try {
      const summary = { total: 0, passed: 0, failed: 0, skipped: 0, errors: 0 };
      await writeCoverageJSON([], summary, '/nonexistent/dir/coverage.json');
      assert.ok(stderrMessages.some(m => m.includes('Failed to write coverage JSON')));
    } finally {
      console.error = origError;
    }
  });
});
