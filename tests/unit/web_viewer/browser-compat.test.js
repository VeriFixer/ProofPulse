import { strict as assert } from 'node:assert';
import { test, describe } from 'node:test';
import { readFile } from 'node:fs/promises';
import { resolve, dirname, join } from 'node:path';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
import vm from 'node:vm';

const execFileAsync = promisify(execFile);
const __dirname = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(__dirname, '../../..');
const BUNDLE_PATH = join(PROJECT_ROOT, 'web_viewer/spans_provider.js');
const BUILD_SCRIPT = join(PROJECT_ROOT, 'web_viewer/build-spans-provider.mjs');

describe('browser bundle compatibility', () => {
  test('spans_provider.js loads and parseProof works without process global', async () => {
    // Rebuild to ensure bundle is fresh
    await execFileAsync('node', [BUILD_SCRIPT], { cwd: PROJECT_ROOT });

    const bundleCode = await readFile(BUNDLE_PATH, 'utf8');

    // Simulate browser: window exists, process does not
    const sandbox = {
      window: {},
      console,
      setTimeout,
      clearTimeout,
    };
    // Explicitly no 'process' in sandbox

    const context = vm.createContext(sandbox);
    vm.runInContext(bundleCode, context);

    assert.equal(typeof sandbox.window.parseProof, 'function',
      'window.parseProof should be a function');
  });

  test('parseProof returns valid result in browser-like context', async () => {
    const bundleCode = await readFile(BUNDLE_PATH, 'utf8');

    const sandbox = {
      window: {},
      console,
      setTimeout,
      clearTimeout,
    };

    const context = vm.createContext(sandbox);
    vm.runInContext(bundleCode, context);

    const log = [
      '  Assertion batch 0:',
      '  Assertions:',
      '    test.dfy(3, 11)-(3, 19): this postcondition holds',
      '  Proof dependencies:',
      '    test.dfy(3, 11)-(3, 19): ensures clause',
    ].join('\n');

    const result = sandbox.window.parseProof('line1\nline2\nline3', log);
    assert.ok(result, 'parseProof should return a result');
    assert.ok(result.proofGraph, 'result should have proofGraph');

    const topNodes = result.proofGraph.getAllTopNodes();
    assert.equal(topNodes.length, 1, 'should have 1 top node');
    assert.equal(topNodes[0].id, 'test.dfy:3,11-3,19');
  });

  test('parseProof with point-only top works without process (no strict mode in browser)', async () => {
    const bundleCode = await readFile(BUNDLE_PATH, 'utf8');

    const sandbox = {
      window: {},
      console,
      setTimeout,
      clearTimeout,
    };

    const context = vm.createContext(sandbox);
    vm.runInContext(bundleCode, context);

    // Point-only top with NO matching range — in browser (no process), strict mode is off
    // so it should NOT throw, just keep the point node
    const log = [
      '  Assertion batch 0:',
      '  Assertions:',
      '    test.dfy(5, 10): this postcondition holds',
      '  Proof dependencies:',
      '    test.dfy(99, 1)-(99, 5): ensures clause',
    ].join('\n');

    // Should not throw in browser context (STRICT_SPAN_MERGE is false)
    assert.doesNotThrow(() => {
      sandbox.window.parseProof('line1\nline2\nline3\nline4\nline5', log);
    });
  });
});
