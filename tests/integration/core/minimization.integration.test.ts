import { describe, it, expect } from "vitest";
import { execFileSync, execSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { resolve, join } from "node:path";
import { runDafny } from "../../../core/src/dafny-runner.js";

const DIST_DIR = resolve(__dirname, "..", "..", "..", "core", "dist", "minimization");
const WRAPPER_JS = join(DIST_DIR, "wrapper.js");
const FIXTURE = resolve(__dirname, "..", "..", "test_data", "output.smt2.1");
const TRIVIAL_DFY = resolve(__dirname, "..", "..", "test_data", "trivial.dfy");

function findExecutable(name: string): string | null {
  const pathEnv = process.env.PATH ?? "";
  const parts = pathEnv.split(process.platform === "win32" ? ";" : ":");
  const exts = process.platform === "win32" ? [".exe", ".cmd", ".bat", ""] : [""];
  for (const p of parts) {
    if (!p) continue;
    for (const ext of exts) {
      try {
        const candidate = join(p, name + ext);
        // eslint-disable-next-line node/no-sync
        const stat = require("fs").statSync(candidate);
        if (stat && stat.isFile()) return candidate;
      } catch {
        // ignore
      }
    }
  }
  return null;
}

const z3Path = findExecutable("z3");
const describeIfZ3 = z3Path ? describe : describe.skip;

function isDafnyAvailable(): boolean {
  try {
    execSync("dafny --version", { stdio: "pipe" });
    return true;
  } catch {
    return false;
  }
}

const hasDafny = isDafnyAvailable();

describeIfZ3("minimization integration", () => {
  it("wrapper + real Z3 on fixture: aux$assume$id14 absent from minimized unsat core", () => {
    const input = readFileSync(FIXTURE, "utf-8");
    const result = execFileSync(
      "node",
      [WRAPPER_JS],
      {
        input,
        encoding: "utf-8",
        timeout: 120_000,
        env: {
          ...process.env,
          PROOFPULSE_Z3_PATH: z3Path!,
        },
      },
    );
    // The minimized output should not contain aux$assume$id14 in any unsat core
    expect(result).not.toMatch(/aux\$assume\$id14/);
  });

  it.skipIf(!hasDafny)("runDafny with forceMinimization: true on trivial .dfy completes without error", async () => {
    const result = await runDafny(TRIVIAL_DFY, {
      forceMinimization: true,
      timeoutSeconds: 120,
    });
    expect(result.error).toBeUndefined();
    expect(result.timedOut).toBeFalsy();
  }, 180_000);
});
