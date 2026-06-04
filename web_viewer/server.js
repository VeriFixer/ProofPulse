import { createServer } from 'node:http';
import { readFile as fsReadFile, writeFile, mkdir, rename } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, extname, resolve, dirname, basename } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { runDafny } from '@proofpulse/core';

const __dirname = dirname(fileURLToPath(import.meta.url));

// --- Cache helpers (inlined from result-cache.ts for ESM compat) ---
const CACHE_DIR = join(homedir(), '.proofpulse', 'cache');

function fileHash(filePath) {
  const absolute = resolve(filePath);
  return createHash('sha256').update(absolute).digest('hex');
}

/** Cache path: {minimized|normal}_{filename}_{hash}.json */
function getCachePath(filePath, minimized) {
  const hash = fileHash(filePath);
  const name = basename(filePath);
  const prefix = minimized ? 'minimized' : 'normal';
  return join(CACHE_DIR, `${prefix}_${name}_${hash}.json`);
}

/** Read cache: checks minimized first, then normal. */
async function readCache(filePath) {
  try {
    const raw = await fsReadFile(getCachePath(filePath, true), 'utf8');
    return JSON.parse(raw);
  } catch { /* miss */ }
  try {
    const raw = await fsReadFile(getCachePath(filePath, false), 'utf8');
    return JSON.parse(raw);
  } catch {
    return null;
  }
}

async function writeCache(filePath, source, log, minimized) {
  const cachePath = getCachePath(filePath, minimized);
  const data = { source, log, minimized, timestamp: Date.now(), filePath };
  try {
    await mkdir(dirname(cachePath), { recursive: true });
    const tmp = cachePath + '.tmp';
    await writeFile(tmp, JSON.stringify(data), 'utf8');
    await rename(tmp, cachePath);
  } catch {
    // Cache write failure is non-fatal
  }
}
// --- End cache helpers ---

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
 * Start HTTP server serving static files and /api/coverage.
 * @param {number} [port=8080]
 * @param {{ source: string, log: string, error?: string, exitCode?: number } | null} [coverageData=null]
 * @returns {Promise<import('node:http').Server>}
 */
export function startServer(port = 8080, coverageData = null) {
  const srcDir = __dirname;

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

    // API: coverage data
    if (pathname === '/api/coverage' && req.method === 'GET') {
      if (!coverageData) {
        res.writeHead(500, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'No coverage data available' }));
        return;
      }
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify(coverageData));
      return;
    }

    // Route / to index.html
    const filePath = pathname === '/'
      ? join(srcDir, 'index.html')
      : join(srcDir, pathname.slice(1));

    // Serve static file
    try {
      const data = await fsReadFile(filePath);
      const ext = extname(filePath);
      const mime = MIME_TYPES[ext] || 'application/octet-stream';
      res.writeHead(200, { 'Content-Type': mime });
      res.end(data);
    } catch {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      res.end('Not Found');
    }
  });

  return new Promise((resolvePromise, reject) => {
    server.on('error', reject);
    server.listen(port, () => {
      const addr = server.address();
      const actualPort = typeof addr === 'object' && addr ? addr.port : port;
      console.log(`Server running at http://localhost:${actualPort}/`);
      resolvePromise(server);
    });
  });
}

/**
 * Compute coverage for a .dfy file. Checks cache first, falls back to runDafny.
 * Returns coverage data object or throws with { status, body } for HTTP errors.
 * @param {string} filePath
 * @param {{ dafnyPath?: string, timeoutSeconds?: number, forceMinimization?: boolean }} [options]
 * @returns {Promise<{ source: string, log: string, fromCache: boolean, cacheTimestamp?: number, minimized?: boolean, error?: string, exitCode?: number }>}
 */
export async function computeCoverage(filePath, options) {
  const resolved = resolve(filePath);

  if (!existsSync(resolved)) {
    const err = new Error(`File not found: ${filePath}`);
    err.httpStatus = 404;
    err.httpBody = { error: `File not found: ${filePath}` };
    throw err;
  }

  if (!resolved.endsWith('.dfy')) {
    const err = new Error(`Not a .dfy file: ${filePath}`);
    err.httpStatus = 400;
    err.httpBody = { error: `Not a .dfy file: ${filePath}` };
    throw err;
  }

  // Check cache first
  const cached = await readCache(resolved);
  if (cached) {
    return {
      source: cached.source,
      log: cached.log,
      fromCache: true,
      cacheTimestamp: cached.timestamp,
      minimized: cached.minimized,
    };
  }

  // Cache miss — run dafny
  const source = await fsReadFile(resolved, 'utf8');

  let result;
  try {
    result = await runDafny(resolved, options);
  } catch {
    const err = new Error('dafny not available');
    err.httpStatus = 500;
    err.httpBody = { error: 'dafny not available' };
    throw err;
  }

  if (result.error && result.error.includes('not found')) {
    const err = new Error('dafny not available');
    err.httpStatus = 500;
    err.httpBody = { error: 'dafny not available' };
    throw err;
  }

  if (result.timedOut) {
    const err = new Error('Verification timed out');
    err.httpStatus = 504;
    err.httpBody = { error: 'Verification timed out' };
    throw err;
  }

  const coverage = { source, log: result.log, fromCache: false };
  if (result.error) coverage.error = result.error;
  if (result.exitCode !== undefined && result.exitCode !== 0) coverage.exitCode = result.exitCode;

  // Write cache (non-blocking, non-fatal)
  const minimized = !!(options && options.forceMinimization);
  await writeCache(resolved, source, result.log, minimized);

  return coverage;
}

/**
 * Parse CLI arguments from argv.
 * Supports: --file <path> --dafny-path <path> --timeout <sec> --force-minimization
 * @param {string[]} argv
 * @returns {{ file: string|null, dafnyPath?: string, timeout?: number, forceMinimization?: boolean }}
 */
function parseCLIArgs(argv) {
  const result = { file: null, dafnyPath: undefined, timeout: undefined, forceMinimization: undefined };
  for (let i = 0; i < argv.length; i++) {
    switch (argv[i]) {
      case '--file':
        result.file = argv[++i] ?? null;
        break;
      case '--dafny-path':
        result.dafnyPath = argv[++i];
        break;
      case '--timeout':
        result.timeout = Number(argv[++i]);
        break;
      case '--force-minimization':
        result.forceMinimization = true;
        break;
    }
  }
  return result;
}

// Run directly
const isMain = process.argv[1] && resolve(process.argv[1]) === resolve(fileURLToPath(import.meta.url));
if (isMain) {
  const args = parseCLIArgs(process.argv);
  if (!args.file) {
    process.stderr.write('Usage: node server.js --file <path.dfy> [--dafny-path <path>] [--timeout <sec>] [--force-minimization]\n');
    process.exit(1);
  }

  try {
    const coverageData = await computeCoverage(args.file, {
      dafnyPath: args.dafnyPath,
      timeoutSeconds: args.timeout,
      forceMinimization: args.forceMinimization,
    });
    await startServer(0, coverageData);
  } catch (err) {
    if (err.httpStatus) {
      process.stderr.write(`Error: ${err.message}\n`);
      process.exit(1);
    }
    throw err;
  }
}
