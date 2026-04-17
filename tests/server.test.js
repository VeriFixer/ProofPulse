import { strict as assert } from 'node:assert';
import { test, describe, afterEach } from 'node:test';
import { readFileSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { mkdtemp } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { request as httpRequest } from 'node:http';
import { startServer } from '../src/server.js';

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
    const expected = readFileSync(join(__dirname, '..', 'src', 'index.html'), 'utf8');
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


describe('GET /api/tests', () => {
  let server;
  let port;
  let tmpDir;

  afterEach(() => {
    if (server) { server.close(); server = null; }
    if (tmpDir) { rmSync(tmpDir, { recursive: true, force: true }); tmpDir = null; }
  });

  async function setup(dirs) {
    tmpDir = await mkdtemp(join(tmpdir(), 'api-tests-'));
    for (const [name, files] of Object.entries(dirs)) {
      const dirPath = join(tmpDir, name);
      mkdirSync(dirPath, { recursive: true });
      for (const f of files) {
        writeFileSync(join(dirPath, f), `content of ${f}`);
      }
    }
    server = await startServer(0, tmpDir);
    port = server.address().port;
  }

  test('returns only folders with both .dfy and prover_log.txt', async () => {
    await setup({
      valid_test: ['foo.dfy', 'prover_log.txt'],
      missing_log: ['bar.dfy'],
      missing_dfy: ['prover_log.txt'],
      also_valid: ['baz.dfy', 'prover_log.txt', 'extra.txt'],
    });
    const res = await rawGet(port, '/api/tests');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'application/json');
    const body = JSON.parse(res.text());
    assert.deepEqual(body, ['also_valid', 'valid_test']);
  });

  test('returns empty array when no valid tests', async () => {
    await setup({
      no_dfy: ['prover_log.txt'],
      no_log: ['something.dfy'],
    });
    const res = await rawGet(port, '/api/tests');
    assert.equal(res.status, 200);
    assert.deepEqual(JSON.parse(res.text()), []);
  });

  test('returns sorted names alphabetically', async () => {
    await setup({
      zebra: ['z.dfy', 'prover_log.txt'],
      alpha: ['a.dfy', 'prover_log.txt'],
      middle: ['m.dfy', 'prover_log.txt'],
    });
    const res = await rawGet(port, '/api/tests');
    const body = JSON.parse(res.text());
    assert.deepEqual(body, ['alpha', 'middle', 'zebra']);
  });

  test('returns empty array for empty tests directory', async () => {
    await setup({});
    const res = await rawGet(port, '/api/tests');
    assert.deepEqual(JSON.parse(res.text()), []);
  });
});


describe('GET /api/tests/:name/source and /api/tests/:name/log', () => {
  let server;
  let port;
  let tmpDir;

  afterEach(() => {
    if (server) { server.close(); server = null; }
    if (tmpDir) { rmSync(tmpDir, { recursive: true, force: true }); tmpDir = null; }
  });

  async function setup(dirs) {
    tmpDir = await mkdtemp(join(tmpdir(), 'api-tests-'));
    for (const [name, files] of Object.entries(dirs)) {
      const dirPath = join(tmpDir, name);
      mkdirSync(dirPath, { recursive: true });
      for (const [fname, content] of Object.entries(files)) {
        writeFileSync(join(dirPath, fname), content);
      }
    }
    server = await startServer(0, tmpDir);
    port = server.address().port;
  }

  test('returns .dfy source content as text/plain', async () => {
    await setup({
      mytest: { 'example.dfy': 'method Main() {}', 'prover_log.txt': 'log data' },
    });
    const res = await rawGet(port, '/api/tests/mytest/source');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'text/plain');
    assert.equal(res.text(), 'method Main() {}');
  });

  test('returns prover_log.txt content as text/plain', async () => {
    await setup({
      mytest: { 'example.dfy': 'method Main() {}', 'prover_log.txt': 'log data here' },
    });
    const res = await rawGet(port, '/api/tests/mytest/log');
    assert.equal(res.status, 200);
    assert.equal(res.headers.get('content-type'), 'text/plain');
    assert.equal(res.text(), 'log data here');
  });

  test('returns 404 for missing test folder', async () => {
    await setup({});
    const res = await rawGet(port, '/api/tests/nonexistent/source');
    assert.equal(res.status, 404);
  });

  test('returns 404 for missing test folder (log)', async () => {
    await setup({});
    const res = await rawGet(port, '/api/tests/nonexistent/log');
    assert.equal(res.status, 404);
  });

  test('returns 400 for path traversal in test name', async () => {
    await setup({
      mytest: { 'example.dfy': 'code', 'prover_log.txt': 'log' },
    });
    const res = await rawGet(port, '/api/tests/..%2Fetc/source');
    assert.equal(res.status, 400);
  });

  test('returns 400 for double-dot traversal in test name', async () => {
    await setup({
      mytest: { 'example.dfy': 'code', 'prover_log.txt': 'log' },
    });
    const res = await rawGet(port, '/api/tests/../mytest/source');
    assert.equal(res.status, 400);
  });

  test('returns 404 when test folder has no .dfy file (source)', async () => {
    await setup({
      nodfy: { 'prover_log.txt': 'log' },
    });
    const res = await rawGet(port, '/api/tests/nodfy/source');
    assert.equal(res.status, 404);
  });
});


/** Raw HTTP POST helper — sends JSON body */
function rawPost(port, path, body) {
  return new Promise((resolve, reject) => {
    const data = typeof body === 'string' ? body : JSON.stringify(body);
    const req = httpRequest({
      hostname: 'localhost',
      port,
      path,
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(data),
      },
    }, (res) => {
      const chunks = [];
      res.on('data', c => chunks.push(c));
      res.on('end', () => {
        resolve({
          status: res.statusCode,
          headers: { get: (k) => res.headers[k.toLowerCase()] },
          body: Buffer.concat(chunks),
          text: () => Buffer.concat(chunks).toString('utf8'),
          json: () => JSON.parse(Buffer.concat(chunks).toString('utf8')),
        });
      });
    });
    req.on('error', reject);
    req.end(data);
  });
}

describe('POST /api/run error cases', () => {
  let server;
  let port;

  afterEach(() => {
    if (server) { server.close(); server = null; }
  });

  async function boot() {
    server = await startServer(0);
    port = server.address().port;
  }

  test('empty code string returns 400 with "No code provided"', async () => {
    await boot();
    const res = await rawPost(port, '/api/run', { code: '' });
    assert.equal(res.status, 400);
    const body = res.json();
    assert.equal(body.error, 'No code provided');
  });

  test('whitespace-only code returns 400', async () => {
    await boot();
    const res = await rawPost(port, '/api/run', { code: '   \n\t  ' });
    assert.equal(res.status, 400);
    const body = res.json();
    assert.equal(body.error, 'No code provided');
  });

  test('missing code field returns 400', async () => {
    await boot();
    const res = await rawPost(port, '/api/run', { notCode: 'hello' });
    assert.equal(res.status, 400);
    const body = res.json();
    assert.equal(body.error, 'No code provided');
  });

  test('invalid JSON body returns 400', async () => {
    await boot();
    const res = await rawPost(port, '/api/run', '{not valid json!!!');
    assert.equal(res.status, 400);
    const body = res.json();
    assert.equal(body.error, 'Invalid JSON');
  });

  test('null code field returns 400', async () => {
    await boot();
    const res = await rawPost(port, '/api/run', { code: null });
    assert.equal(res.status, 400);
    const body = res.json();
    assert.equal(body.error, 'No code provided');
  });
});
