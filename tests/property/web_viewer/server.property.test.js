import { strict as assert } from 'node:assert';
import { test, describe } from 'node:test';
import { mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { mkdtemp } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { request as httpRequest } from 'node:http';
import fc from 'fast-check';
import { startServer } from '../../../web_viewer/server.js';

/** Raw HTTP GET helper */
function rawGet(port, path) {
  return new Promise((resolve, reject) => {
    const req = httpRequest({ hostname: 'localhost', port, path, method: 'GET' }, (res) => {
      const chunks = [];
      res.on('data', c => chunks.push(c));
      res.on('end', () => {
        resolve({
          status: res.statusCode,
          headers: { get: (k) => res.headers[k.toLowerCase()] },
          text: () => Buffer.concat(chunks).toString('utf8'),
        });
      });
    });
    req.on('error', reject);
    req.end();
  });
}

/**
 * Validates: Requirements 2.1, 1.1
 *
 * Feature: interactive-coverage-viewer, Property 1: Test listing completeness
 *
 * For any set of subdirectories under the tests root that contain both a .dfy
 * file and a prover_log.txt, GET /api/tests returns exactly those directory
 * names (no more, no fewer), sorted alphabetically.
 */
describe('Feature: interactive-coverage-viewer, Property 1: Test listing completeness', () => {
  test('GET /api/tests returns exactly the valid test dirs, sorted', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(
          fc.record({
            name: fc.stringMatching(/^[a-z][a-z0-9_]{0,11}$/).filter(s => s.length >= 1),
            hasDfy: fc.boolean(),
            hasLog: fc.boolean(),
          }),
          { minLength: 0, maxLength: 8 }
        ).map(entries => {
          // deduplicate by name
          const seen = new Set();
          return entries.filter(e => {
            if (seen.has(e.name)) return false;
            seen.add(e.name);
            return true;
          });
        }),
        async (entries) => {
          let tmpDir;
          let server;
          try {
            tmpDir = await mkdtemp(join(tmpdir(), 'pbt-listing-'));

            // Populate temp directory
            for (const entry of entries) {
              const dirPath = join(tmpDir, entry.name);
              mkdirSync(dirPath, { recursive: true });
              if (entry.hasDfy) {
                writeFileSync(join(dirPath, 'example.dfy'), 'method M() {}');
              }
              if (entry.hasLog) {
                writeFileSync(join(dirPath, 'prover_log.txt'), 'log');
              }
            }

            // Start server on ephemeral port
            server = await startServer(0, tmpDir);
            const port = server.address().port;

            // Fetch /api/tests
            const res = await rawGet(port, '/api/tests');
            assert.equal(res.status, 200);

            const actual = JSON.parse(res.text());

            // Expected: dirs where both hasDfy and hasLog are true, sorted
            const expected = entries
              .filter(e => e.hasDfy && e.hasLog)
              .map(e => e.name)
              .sort();

            assert.deepEqual(actual, expected);
          } finally {
            if (server) server.close();
            if (tmpDir) rmSync(tmpDir, { recursive: true, force: true });
          }
        }
      ),
      { numRuns: 50 }
    );
  });
});


/**
 * Validates: Requirements 1.3, 2.2, 2.3
 *
 * Feature: interactive-coverage-viewer, Property 2: Test file retrieval round-trip
 *
 * For any valid test name, GET /api/tests/:name/source returns content identical
 * to the .dfy file on disk, and GET /api/tests/:name/log returns content identical
 * to prover_log.txt on disk.
 */
describe('Feature: interactive-coverage-viewer, Property 2: Test file retrieval round-trip', () => {
  test('source and log endpoints return byte-identical content to disk', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.stringMatching(/^[a-z][a-z0-9]{0,11}$/).filter(s => s.length >= 1),
        fc.string({ minLength: 0, maxLength: 500 }),
        fc.string({ minLength: 0, maxLength: 500 }),
        async (dirName, dfyContent, logContent) => {
          let tmpDir;
          let server;
          try {
            tmpDir = await mkdtemp(join(tmpdir(), 'pbt-roundtrip-'));
            const testDir = join(tmpDir, dirName);
            mkdirSync(testDir, { recursive: true });
            writeFileSync(join(testDir, 'example.dfy'), dfyContent, 'utf8');
            writeFileSync(join(testDir, 'prover_log.txt'), logContent, 'utf8');

            server = await startServer(0, tmpDir);
            const port = server.address().port;

            // Fetch source
            const srcRes = await rawGet(port, `/api/tests/${dirName}/source`);
            assert.equal(srcRes.status, 200);
            assert.equal(srcRes.headers.get('content-type'), 'text/plain');
            assert.equal(srcRes.text(), dfyContent);

            // Fetch log
            const logRes = await rawGet(port, `/api/tests/${dirName}/log`);
            assert.equal(logRes.status, 200);
            assert.equal(logRes.headers.get('content-type'), 'text/plain');
            assert.equal(logRes.text(), logContent);
          } finally {
            if (server) server.close();
            if (tmpDir) rmSync(tmpDir, { recursive: true, force: true });
          }
        }
      ),
      { numRuns: 50 }
    );
  });
});


/**
 * Validates: Requirements 2.4
 *
 * Feature: interactive-coverage-viewer, Property 3: Invalid test name yields 404
 *
 * For any string that does not correspond to a valid test directory,
 * GET /api/tests/:name/source SHALL return HTTP 404 (or 400 for path traversal).
 */
describe('Feature: interactive-coverage-viewer, Property 3: Invalid test name yields 404', () => {
  test('invalid test names yield 400 or 404', async () => {
    const VALID_TEST = 'validtest';
    let tmpDir;
    let server;
    let port;

    try {
      tmpDir = await mkdtemp(join(tmpdir(), 'pbt-invalid-'));

      // Create one valid test so we know exactly what's valid
      const validDir = join(tmpDir, VALID_TEST);
      mkdirSync(validDir, { recursive: true });
      writeFileSync(join(validDir, 'example.dfy'), 'method M() {}');
      writeFileSync(join(validDir, 'prover_log.txt'), 'log');

      server = await startServer(0, tmpDir);
      port = server.address().port;

      // Property: arbitrary strings that are NOT the valid test name get 400 or 404
      await fc.assert(
        fc.asyncProperty(
          fc.string({ minLength: 1, maxLength: 40 }),
          async (name) => {
            // Skip the one valid name
            fc.pre(name !== VALID_TEST);

            const encoded = encodeURIComponent(name);
            const res = await rawGet(port, `/api/tests/${encoded}/source`);
            assert.ok(
              res.status === 400 || res.status === 404,
              `Expected 400 or 404 for "${name}", got ${res.status}`
            );
          }
        ),
        { numRuns: 50 }
      );

      // Explicit path traversal strings
      const traversals = ['../etc', '..%2Fetc', '..', '../..', '.%2e', '%2e.', '%2e%2e'];
      for (const t of traversals) {
        const res = await rawGet(port, `/api/tests/${t}/source`);
        assert.ok(
          res.status === 400 || res.status === 404,
          `Expected 400 or 404 for traversal "${t}", got ${res.status}`
        );
      }
    } finally {
      if (server) server.close();
      if (tmpDir) rmSync(tmpDir, { recursive: true, force: true });
    }
  });
});


/**
 * Validates: Requirements 5.1
 *
 * Feature: interactive-coverage-viewer, Property 4: Static file serving round-trip
 *
 * For each file in src/, verify HTTP response matches fs.readFileSync from disk.
 * Exhaustive check over all regular files in src/ (excluding test files).
 */
describe('Feature: interactive-coverage-viewer, Property 4: Static file serving round-trip', () => {
  test('each static file served via HTTP matches disk content', async () => {
    const { readdirSync, readFileSync, statSync } = await import('node:fs');
    const { dirname, join } = await import('node:path');
    const { fileURLToPath } = await import('node:url');

    const srcDir = dirname(fileURLToPath(import.meta.url));
    const allEntries = readdirSync(srcDir);
    const files = allEntries.filter(f => {
      const full = join(srcDir, f);
      if (!statSync(full).isFile()) return false;
      if (f.endsWith('.test.js')) return false;
      return true;
    });

    assert.ok(files.length > 0, 'Expected at least one servable file in src/');

    let server;
    try {
      server = await startServer(0);
      const port = server.address().port;

      for (const file of files) {
        const diskContent = readFileSync(join(srcDir, file));
        const res = await rawGet(port, `/${file}`);
        assert.equal(res.status, 200, `Expected 200 for /${file}, got ${res.status}`);

        const httpBody = Buffer.from(res.text(), 'utf8');
        assert.deepEqual(httpBody, diskContent, `Content mismatch for /${file}`);
      }
    } finally {
      if (server) server.close();
    }
  });
});
