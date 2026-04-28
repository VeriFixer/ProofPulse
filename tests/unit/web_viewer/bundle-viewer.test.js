import { strict as assert } from 'node:assert';
import { test, describe, beforeEach, afterEach } from 'node:test';
import { mkdtemp, rm, writeFile, mkdir, access } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { constants } from 'node:fs';

const execFileAsync = promisify(execFile);
const SCRIPT = resolve('web_viewer/bundle-viewer.sh');

describe('bundle-viewer.sh output structure', () => {
  let tmpDir;
  let dfyDir;
  let outDir;

  beforeEach(async () => {
    tmpDir = await mkdtemp(join(tmpdir(), 'bundle-test-'));
    dfyDir = join(tmpDir, 'input');
    outDir = join(tmpDir, 'output');
    await mkdir(dfyDir, { recursive: true });

    // Create dummy .dfy file and prover_log.txt
    await writeFile(join(dfyDir, 'example.dfy'), 'method Main() {}');
    await writeFile(join(dfyDir, 'prover_log.txt'), 'prover log content');
  });

  afterEach(async () => {
    await rm(tmpDir, { recursive: true, force: true });
  });

  test('produces all expected files in output directory', async () => {
    const dfyFile = join(dfyDir, 'example.dfy');

    await execFileAsync('bash', [SCRIPT, dfyFile, outDir]);

    const expected = [
      'index.html',
      'app.js',
      'styles.css',
      'spans_provider.js',
      'source_code.dfy',
      'prover_log.txt',
    ];

    for (const file of expected) {
      await access(join(outDir, file), constants.F_OK);
    }
  });

  test('copied dfy file is renamed to source_code.dfy', async () => {
    const dfyFile = join(dfyDir, 'example.dfy');

    await execFileAsync('bash', [SCRIPT, dfyFile, outDir]);

    const { readFile: rf } = await import('node:fs/promises');
    const content = await rf(join(outDir, 'source_code.dfy'), 'utf8');
    assert.equal(content, 'method Main() {}');
  });

  test('prover_log.txt is copied from dfy file directory', async () => {
    const dfyFile = join(dfyDir, 'example.dfy');

    await execFileAsync('bash', [SCRIPT, dfyFile, outDir]);

    const { readFile: rf } = await import('node:fs/promises');
    const content = await rf(join(outDir, 'prover_log.txt'), 'utf8');
    assert.equal(content, 'prover log content');
  });
});
