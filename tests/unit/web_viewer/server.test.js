import { strict as assert } from 'node:assert';
import { test, describe, afterEach } from 'node:test';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { request as httpRequest } from 'node:http';
import { startServer } from '../../../web_viewer/server.js';

const __dirname = dirname(fileURLToPath(import.meta.url));

/** Raw HTTP request that does NOT normalize the URL path */
function rawGet(port, path) {
  return new Promise((resolve, reject) => {
    const req = httpRequest({ hostname: 'localhost', port, path, method: 'GET' }, (res) => {
      const chunks = [];
      res.on('data', c => chunks.push(c));
      res.on('end', () => {
        resolve({
          status: res.statusCode,
          headers: { get: (k) => res.headers[k.toLowerCase()] },
          body: Buffer.concat(chunks),
          text: () => Buffer.concat(chunks).toString('utf8'),
        });
      });
    });
    req.on('error', reject);
    req.end();
  });
}

describe('startServer static file serving', () => {
  let server;
  let baseUrl;
  let port;

  afterEach(() => {
    if (server) {
      server.close();
      server = null;
    }
  });

  async function boot() {
    server = await startServer(0); // ephemeral port
    const addr = server.address();
    baseUrl = `http://localhost:${addr.port}`;
    port = addr.port;
  }

  test('/ serves index.html', async () => {
    await boot();
    const res = await rawGet(port, '/');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'text/html');
    const body = res.text();
    const expected = readFileSync(join(__dirname, '..', '..', '..', 'web_viewer', 'index.html'), 'utf8');
    assert.equal(body, expected);
  });

  test('/styles.css serves with correct MIME', async () => {
    await boot();
    const res = await rawGet(port, '/styles.css');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'text/css');
  });

  test('/app.js serves with correct MIME', async () => {
    await boot();
    const res = await rawGet(port, '/app.js');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'text/javascript');
  });

  test('path traversal returns 400', async () => {
    await boot();
    const res = await rawGet(port, '/../package.json');
    assert.equal(res.status, 400);
  });

  test('encoded path traversal returns 400', async () => {
    await boot();
    const res = await rawGet(port, '/%2e%2e/package.json');
    assert.equal(res.status, 400);
  });

  test('nonexistent file returns 404', async () => {
    await boot();
    const res = await rawGet(port, '/does-not-exist.xyz');
    assert.equal(res.status, 404);
  });

  test('configurable port works', async () => {
    server = await startServer(0);
    const addr = server.address();
    assert.ok(addr.port > 0);
  });
});


describe('GET /api/coverage', () => {
  let server;
  let port;

  afterEach(() => {
    if (server) { server.close(); server = null; }
  });

  test('returns 500 with error when no coverage data provided', async () => {
    server = await startServer(0);
    port = server.address().port;
    const res = await rawGet(port, '/api/coverage');
    assert.equal(res.status, 500);
    const body = JSON.parse(res.text());
    assert.equal(body.error, 'No coverage data available');
  });

  test('returns 200 with coverage data when provided', async () => {
    const data = { source: 'method M() {}', log: 'some log', exitCode: 0 };
    server = await startServer(0, data);
    port = server.address().port;
    const res = await rawGet(port, '/api/coverage');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'application/json');
    const body = JSON.parse(res.text());
    assert.deepEqual(body, data);
  });

  test('returns coverage data with error field when present', async () => {
    const data = { source: 'code', log: 'log', error: 'verification failed', exitCode: 1 };
    server = await startServer(0, data);
    port = server.address().port;
    const res = await rawGet(port, '/api/coverage');
    assert.equal(res.status, 200);
    const body = JSON.parse(res.text());
    assert.equal(body.error, 'verification failed');
    assert.equal(body.exitCode, 1);
  });
});
