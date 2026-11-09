import { afterEach, describe, expect, it } from "vitest";
import { spawn } from "node:child_process";
import { chmodSync, copyFileSync, existsSync, mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { runDafny, type DafnyRunResult } from "../backends/dafny/runner.js";
import { RunStatus } from "../backends/backend.js";

// A stand-in Dafny (fixtures/fake-dafny.mjs) that verifies two methods,
// "First" then "Second", 300 ms apart.
const dir = mkdtempSync(join(tmpdir(), "proofpulse-runner-test-"));
const fakeDafny = join(dir, "dafny");
copyFileSync(resolve(__dirname, "fixtures", "fake-dafny.mjs"), fakeDafny);
chmodSync(fakeDafny, 0o755);
const source = resolve(__dirname, "fixtures", "unproved-under-tracking.dfy");

const ENV = ["FAKE_DAFNY_ARGS", "FAKE_DAFNY_HANG", "FAKE_DAFNY_CHILD_PID", "FAKE_DAFNY_RUN_MS"] as const;
afterEach(() => { for (const k of ENV) delete process.env[k]; });

const isAlive = (pid: number): boolean => {
  try { process.kill(pid, 0); return true; } catch { return false; }
};

describe.skipIf(process.platform === "win32")("Dafny runner", () => {
  it("reports each method's results while Dafny is still running", async () => {
    process.env.FAKE_DAFNY_RUN_MS = "1500";
    const partial: DafnyRunResult[] = [];
    const result = await runDafny(source, { toolPath: fakeDafny, onPartialResult: (r) => partial.push(r) });

    expect(result.status).toBe(RunStatus.Completed);
    expect(partial.length).toBeGreaterThan(0);
    expect(partial[0].log).toContain("Results for First");
    expect(partial[0].log).not.toContain("Results for Second");
    expect(partial.at(-1)!.log).toContain("Results for Second");
  });

  it("keeps the methods that finished when the whole-run time limit is hit", { timeout: 15_000 }, async () => {
    process.env.FAKE_DAFNY_HANG = "1";
    process.env.FAKE_DAFNY_CHILD_PID = join(dir, "child.pid");
    const result = await runDafny(source, { toolPath: fakeDafny, totalTimeoutSeconds: 2 });

    expect(result.status).toBe(RunStatus.TimedOut);
    expect(result.log).toContain("Results for First");
    expect(result.log).toContain("Results for Second");
  });

  it("stops the processes Dafny started when the run is stopped", { timeout: 15_000 }, async () => {
    process.env.FAKE_DAFNY_HANG = "1";
    process.env.FAKE_DAFNY_CHILD_PID = join(dir, "child-abort.pid");
    const pidFile = process.env.FAKE_DAFNY_CHILD_PID;
    const controller = new AbortController();
    // Stop the run once Dafny has started its child process.
    const poll = setInterval(() => { if (existsSync(pidFile)) controller.abort(); }, 50);
    const result = await runDafny(source, { toolPath: fakeDafny, signal: controller.signal });
    clearInterval(poll);

    expect(result.status).toBe(RunStatus.Aborted);
    const child = Number(readFileSync(pidFile, "utf8"));
    await new Promise((r) => setTimeout(r, 300));
    expect(isAlive(child)).toBe(false);
  });

  it("does not stop the whole run at the time limit for one goal", async () => {
    process.env.FAKE_DAFNY_RUN_MS = "1500";
    const result = await runDafny(source, { toolPath: fakeDafny, timeoutSeconds: 1 });

    expect(result.status).toBe(RunStatus.Completed);
    expect(result.log).toContain("Results for Second");
  });

  it("does not turn on z3's own core minimization", async () => {
    // With smt/sat.core.minimize, z3 can run far past the goal's time limit
    // (minutes, gigabytes); the z3 wrapper checks and minimizes cores itself.
    process.env.FAKE_DAFNY_ARGS = join(dir, "args.json");
    await runDafny(source, { toolPath: fakeDafny });

    const args: string[] = JSON.parse(readFileSync(process.env.FAKE_DAFNY_ARGS, "utf8"));
    expect(args.join(" ")).not.toMatch(/core\.minimize/);
  });
});

describe.skipIf(process.platform === "win32")("CLI --stream", () => {
  const readOr = (path: string): string => (existsSync(path) ? readFileSync(path, "utf8") : "");

  it("writes each method's findings to the file as soon as the method is verified", async () => {
    const streamFile = join(dir, "stream.txt");
    const cli = spawn("npx", ["tsx", "src/cli.ts", source, "--dafny-path", fakeDafny, "--stream", streamFile], {
      cwd: resolve(__dirname, "..", ".."),
      env: { ...process.env, FAKE_DAFNY_RUN_MS: "3000" },
      stdio: "ignore",
    });
    const exited = new Promise<number | null>((r) => cli.on("close", r));

    // Before Dafny finishes, the file holds the first method only.
    let midRun = "";
    for (let i = 0; i < 100 && !midRun.includes("Second"); i++) {
      midRun = readOr(streamFile);
      if (midRun.includes("First")) break;
      await new Promise((r) => setTimeout(r, 100));
    }
    expect(midRun).toContain("First");
    expect(midRun).not.toContain("Second");

    expect(await exited).toBe(0);
    const done = readOr(streamFile);
    expect(done).toContain("First");
    expect(done).toContain("Second");
  }, 30_000);
});
