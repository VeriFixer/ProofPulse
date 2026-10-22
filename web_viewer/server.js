import { createServer } from 'node:http';
import { readFile as fsReadFile, writeFile, mkdir, rename } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, extname, resolve, dirname, basename } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { homedir } from 'node:os';
import { assertNever, createDefaultRegistry, parseCoverageReport, RunStatus, VerifierId } from '@proofpulse/core';

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

const registry = createDefaultRegistry();

/** Throw an error carrying the HTTP status/body the server should answer with. */
function httpError(status, message) {
  const err = new Error(message);
  err.httpStatus = status;
  err.httpBody = { error: message };
  return err;
}

/**
 * Compute coverage for a source file. Checks cache first, falls back to running
 * the file's verifier backend (or loads a saved coverage report).
 * Returns coverage data object or throws with { status, body } for HTTP errors.
 * @param {string} filePath
 * @param {{ backendOptions?: import('@proofpulse/core').BackendOptions, reportPath?: string, minimized?: boolean }} [options]
 * @returns {Promise<{ source: string, log?: string, report?: object, fromCache: boolean, cacheTimestamp?: number, minimized?: boolean, error?: string, exitCode?: number }>}
 */
export async function computeCoverage(filePath, options = {}) {
  const resolved = resolve(filePath);

  if (!existsSync(resolved)) {
    throw httpError(404, `File not found: ${filePath}`);
  }

  const backend = registry.backendForFile(resolved);
  if (!backend) {
    throw httpError(400, `Not a supported file (${registry.fileExtensions().join(', ')}): ${filePath}`);
  }

  const source = await fsReadFile(resolved, 'utf8');

  // A saved coverage report: no verifier run, no cache.
  if (options.reportPath) {
    try {
      const report = parseCoverageReport(await fsReadFile(options.reportPath, 'utf8'));
      return { source, report, fromCache: false };
    } catch (e) {
      throw httpError(400, `Invalid coverage report ${options.reportPath}: ${e.message}`);
    }
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

  // Cache miss — run the verifier
  let result;
  try {
    result = await backend.run(resolved, options.backendOptions ?? {});
  } catch {
    throw httpError(500, `${backend.displayName} not available`);
  }

  switch (result.status) {
    case RunStatus.Completed:
    case RunStatus.Aborted:
      break;
    case RunStatus.TimedOut:
      throw httpError(504, 'Verification timed out');
    case RunStatus.Failed:
      if (result.errorMessage && result.errorMessage.includes('not found')) {
        throw httpError(500, `${backend.displayName} not available`);
      }
      break;
    default:
      assertNever(result.status, 'run status');
  }

  const log = result.rawLog ?? '';
  const coverage = { source, log, fromCache: false };
  if (result.report) coverage.report = result.report;
  if (result.status !== RunStatus.Completed) coverage.error = result.errorMessage ?? result.status;
  if (result.exitCode !== undefined && result.exitCode !== 0) coverage.exitCode = result.exitCode;

  // Write cache (non-blocking, non-fatal)
  const minimized = options.backendOptions?.minimization !== undefined;
  await writeCache(resolved, source, log, minimized);

  return coverage;
}

/**
 * Parse CLI arguments from argv.
 * Supports: --file <path> --dafny-path <path> --timeout <sec> --force-minimization
 *           --no-abstract-interpretation --report <coverage-report.yaml|json>
 * @param {string[]} argv
 */
function parseCLIArgs(argv) {
  const result = {
    file: null,
    dafnyPath: undefined,
    timeout: undefined,
    forceMinimization: false,
    noAbstractInterpretation: false,
    reportPath: undefined,
  };
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
      case '--no-abstract-interpretation':
        result.noAbstractInterpretation = true;
        break;
      case '--report':
        result.reportPath = argv[++i];
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
    process.stderr.write('Usage: node server.js --file <path> [--dafny-path <path>] [--timeout <sec>] [--force-minimization] [--no-abstract-interpretation] [--report <coverage-report>]\n');
    process.exit(1);
  }

  try {
    const coverageData = await computeCoverage(args.file, {
      reportPath: args.reportPath,
      backendOptions: {
        toolPath: args.dafnyPath,
        timeoutSeconds: args.timeout,
        ...(args.forceMinimization ? { minimization: {} } : {}),
        backendOptions: { backend: VerifierId.Dafny, noAbstractInterpretation: args.noAbstractInterpretation },
      },
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
