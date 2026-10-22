import { strict as assert } from 'node:assert';
import { test, describe } from 'node:test';
import { request as httpRequest } from 'node:http';
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
 * Validates: Requirements 5.1
 *
 * Feature: interactive-coverage-viewer, Property 4: Static file serving round-trip
 *
 * For each static viewer file in web_viewer/, verify the HTTP response matches
 * the file on disk.
 */
describe('Feature: interactive-coverage-viewer, Property 4: Static file serving round-trip', () => {
  test('each static file served via HTTP matches disk content', async () => {
    const { readdirSync, readFileSync, statSync } = await import('node:fs');
    const { dirname, join } = await import('node:path');
    const { fileURLToPath } = await import('node:url');

    const srcDir = join(dirname(fileURLToPath(import.meta.url)), '..', '..', '..', 'web_viewer');
    const STATIC_EXTENSIONS = ['.html', '.css', '.js'];
    const files = readdirSync(srcDir).filter(f =>
      statSync(join(srcDir, f)).isFile() && STATIC_EXTENSIONS.some(ext => f.endsWith(ext)),
    );

    assert.ok(files.length > 0, 'Expected at least one servable file in web_viewer/');

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
