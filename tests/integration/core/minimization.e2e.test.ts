import { describe, it, expect } from "vitest";
import { resolve } from "node:path";
import { runDafny } from "../../../core/src/backends/dafny/runner.js";
import { RunStatus } from "../../../core/src/backends/backend.js";

function findExecutable(name: string): string | null {
  const pathEnv = process.env.PATH ?? "";
  const parts = pathEnv.split(process.platform === "win32" ? ";" : ":");
  const exts = process.platform === "win32" ? [".exe", ".cmd", ".bat", ""] : [""];
  for (const p of parts) {
    if (!p) continue;
    for (const ext of exts) {
      try {
        const candidate = require("path").join(p, name + ext);
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

const dafnyBin = findExecutable("dafny");
const z3Bin = findExecutable("z3");

const describeIfEnv = dafnyBin && z3Bin ? describe : describe.skip;

const TRIVIAL_DFY = resolve(__dirname, "..", "..", "test_data", "trivial.dfy");

describeIfEnv("minimization end-to-end", () => {
  it("runDafny with minimization completes without error", async () => {
    const result = await runDafny(TRIVIAL_DFY, {
      minimization: {},
      timeoutSeconds: 120,
    });

    expect(result.errorMessage).toBeUndefined();
    expect(result.status).toBe(RunStatus.Completed);
  }, 180_000);
});
