import { describe, it, expect, beforeAll, afterAll } from "vitest";
import { runDafny } from "../../../core/src/dafny-runner.js";
import { mkdtemp, writeFile, chmod, rm } from "node:fs/promises";
import { join, resolve } from "node:path";
import { tmpdir } from "node:os";

/**
 * Unit tests for spawnDafny abort behavior (tested via public runDafny).
 * Uses a fake dafny script that responds to --version and sleeps on verify.
 *
 * Validates: Requirements 2.1, 2.2, 2.3, 8.2, 8.3
 */

const TEST_DFY = resolve(__dirname, "../../../tests/test_data/trivial.dfy");

let fakeDafnyPath: string;
let tmpDir: string;

beforeAll(async () => {
  tmpDir = await mkdtemp(join(tmpdir(), "abort-test-"));
  fakeDafnyPath = join(tmpDir, "fake-dafny");

  // Script: prints version for --version, sleeps 30s for verify
  const script = `#!/bin/bash
if [[ "$1" == "--version" || "$1" == "/version" ]]; then
  echo "4.0.0-test"
  exit 0
fi
# For verify command, sleep long
sleep 30
`;
  await writeFile(fakeDafnyPath, script, "utf8");
  await chmod(fakeDafnyPath, 0o755);
});

afterAll(async () => {
  await rm(tmpDir, { recursive: true, force: true }).catch(() => {});
});

describe("runDafny abort behavior", () => {
  it("pre-aborted signal returns immediately with error 'aborted'", async () => {
    const controller = new AbortController();
    controller.abort(); // abort before calling

    const start = Date.now();
    const result = await runDafny(TEST_DFY, {
      dafnyPath: fakeDafnyPath,
      signal: controller.signal,
    });
    const elapsed = Date.now() - start;

    expect(result.error).toBe("aborted");
    expect(elapsed).toBeLessThan(1000); // should return almost instantly
  });

  it("mid-run abort kills process and returns error 'aborted'", async () => {
    const controller = new AbortController();

    const start = Date.now();
    const resultPromise = runDafny(TEST_DFY, {
      dafnyPath: fakeDafnyPath,
      signal: controller.signal,
      timeoutSeconds: 30,
    });

    // Abort after 50ms (while fake dafny is sleeping)
    setTimeout(() => controller.abort(), 50);

    const result = await resultPromise;
    const elapsed = Date.now() - start;

    expect(result.error).toBe("aborted");
    expect(elapsed).toBeLessThan(2000); // should resolve well before timeout
  });
});
