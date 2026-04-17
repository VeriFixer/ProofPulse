import { createServer } from 'node:http';
import { readFile, readdir, writeFile, mkdtemp, rm } from 'node:fs/promises';
import { join, extname, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';
import { spawn } from 'node:child_process';

const __dirname = dirname(fileURLToPath(import.meta.url));

const MIME_TYPES = {
  '.html': 'text/html',
  '.js':   'text/javascript',
  '.css':  'text/css',
  '.json': 'application/json',
  '.png':  'image/png',
  '.svg':  'image/svg+xml',
  '.txt':  'text/plain',
  '.dfy':  'text/plain',
};

/**
 * Start HTTP server serving static files from src/ and API routes.
 * @param {number} [port=8080]
 * @param {string} [testsRoot='dataset/tests']
 * @param {number} [timeoutSec=60]
 * @returns {Promise<import('node:http').Server>}
 */
export function startServer(port = 8080, testsRoot = 'dataset/tests', timeoutSec = 60) {
  const srcDir = __dirname; // src/ directory

  const server = createServer(async (req, res) => {
    const raw = req.url;

    // Reject path traversal on raw URL (before any decoding/normalization)
    if (raw.includes('..') || raw.includes('%2e%2e') || raw.includes('%2E%2E') || raw.includes('%2e.') || raw.includes('.%2e') || raw.includes('%2E.') || raw.includes('.%2E')) {
      res.writeHead(400, { 'Content-Type': 'text/plain' });
      res.end('Bad Request: path traversal not allowed');
      return;
    }

    const url = new URL(raw, `http://${req.headers.host}`);
    const pathname = decodeURIComponent(url.pathname);

    // Double-check decoded path for traversal
    if (pathname.includes('..')) {
      res.writeHead(400, { 'Content-Type': 'text/plain' });
      res.end('Bad Request: path traversal not allowed');
      return;
    }

    // API: list test folders
    if (pathname === '/api/tests' && req.method === 'GET') {
      try {
        const entries = await readdir(testsRoot, { withFileTypes: true });
        const dirs = entries.filter(e => e.isDirectory());
        const valid = [];
        for (const dir of dirs) {
          const files = await readdir(join(testsRoot, dir.name));
          const hasDfy = files.some(f => f.endsWith('.dfy'));
          const hasLog = files.includes('prover_log.txt');
          if (hasDfy && hasLog) valid.push(dir.name);
        }
        valid.sort();
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify(valid));
      } catch {
        res.writeHead(500, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Failed to list tests' }));
      }
      return;
    }

    // API: get test source or log
    const testFileMatch = pathname.match(/^\/api\/tests\/([^/]+)\/(source|log)$/);
    if (testFileMatch && req.method === 'GET') {
      const testName = testFileMatch[1];
      const fileType = testFileMatch[2];

      // Path traversal check on test name
      if (testName.includes('..')) {
        res.writeHead(400, { 'Content-Type': 'text/plain' });
        res.end('Bad Request: path traversal not allowed');
        return;
      }

      const testDir = join(testsRoot, testName);

      try {
        if (fileType === 'source') {
          // Find the .dfy file in the test folder
          const files = await readdir(testDir);
          const dfyFile = files.find(f => f.endsWith('.dfy'));
          if (!dfyFile) {
            res.writeHead(404, { 'Content-Type': 'text/plain' });
            res.end('Not Found: no .dfy file in test folder');
            return;
          }
          const content = await readFile(join(testDir, dfyFile));
          res.writeHead(200, { 'Content-Type': 'text/plain' });
          res.end(content);
        } else {
          // log
          const content = await readFile(join(testDir, 'prover_log.txt'));
          res.writeHead(200, { 'Content-Type': 'text/plain' });
          res.end(content);
        }
      } catch {
        res.writeHead(404, { 'Content-Type': 'text/plain' });
        res.end('Not Found');
      }
      return;
    }

    // API: run dafny verify on user code
    if (pathname === '/api/run' && req.method === 'POST') {
      let body = '';
      req.on('data', chunk => { body += chunk; });
      await new Promise(r => req.on('end', r));

      let parsed;
      try {
        parsed = JSON.parse(body);
      } catch {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Invalid JSON' }));
        return;
      }

      const code = parsed && parsed.code;
      if (!code || (typeof code === 'string' && code.trim() === '')) {
        res.writeHead(400, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'No code provided' }));
        return;
      }

      let tmpDir;
      try {
        tmpDir = await mkdtemp(join(tmpdir(), 'proofpulse-'));
        const dfyPath = join(tmpDir, 'temp.dfy');
        await writeFile(dfyPath, code, 'utf8');

        const args = [
          'verify', 'temp.dfy',
          '--verification-coverage-report', 'cov',
          '--log-format', 'text',
          '--solver-option', 'LOG_FILE=output.smt2',
          '--bprint', 'output.bpl',
          '--isolate-assertions',
          '--allow-warnings', 'true',
          '--verification-time-limit', String(timeoutSec),
          '--boogie', '/proverOpt:O:smt.core.minimize=true /proverOpt:O:sat.core.minimize=true /proverOpt:C:proof=true',
        ];

        const result = await new Promise(resolveRun => {
          let stdout = '';
          let stderr = '';
          let done = false;

          const child = spawn('dafny', args, { cwd: tmpDir });

          let timedOut = false;
          const timer = setTimeout(() => {
            timedOut = true;
            child.kill('SIGKILL');
          }, timeoutSec * 1000);

          child.stdout.on('data', d => { stdout += d; });
          child.stderr.on('data', d => { stderr += d; });

          child.on('error', err => {
            clearTimeout(timer);
            if (!done) { done = true; resolveRun({ spawnError: err }); }
          });

          child.on('close', exitCode => {
            clearTimeout(timer);
            if (!done) {
              done = true;
              if (timedOut) {
                resolveRun({ timedOut: true });
              } else {
                resolveRun({ exitCode, stdout, stderr });
              }
            }
          });
        });

        if (result.spawnError) {
          res.writeHead(500, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ error: 'dafny not available' }));
          return;
        }

        if (result.timedOut) {
          res.writeHead(504, { 'Content-Type': 'application/json' });
          res.end(JSON.stringify({ error: 'Verification timed out' }));
          return;
        }

        // Read log regardless of exit code — dafny produces coverage
        // data even when some assertions fail
        let log;
        try {
          log = await readFile(join(tmpDir, 'prover_log.txt'), 'utf8');
        } catch {
          log = result.stdout;
        }
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ log, exitCode: result.exitCode }));
      } catch (err) {
        res.writeHead(500, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: err.message }));
      } finally {
        if (tmpDir) {
          rm(tmpDir, { recursive: true, force: true }).catch(() => {});
        }
      }
      return;
    }

    // Route / to index.html
    const filePath = pathname === '/'
      ? join(srcDir, 'index.html')
      : join(srcDir, pathname.slice(1));

    // Serve static file
    try {
      const data = await readFile(filePath);
      const ext = extname(filePath);
      const mime = MIME_TYPES[ext] || 'application/octet-stream';
      res.writeHead(200, { 'Content-Type': mime });
      res.end(data);
    } catch {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      res.end('Not Found');
    }
  });

  return new Promise((resolvePromise) => {
    server.listen(port, () => {
      console.log(`Server running at http://localhost:${port}/`);
      resolvePromise(server);
    });
  });
}

// Run directly
const isMain = process.argv[1] && resolve(process.argv[1]) === resolve(fileURLToPath(import.meta.url));
if (isMain) {
  startServer();
}
