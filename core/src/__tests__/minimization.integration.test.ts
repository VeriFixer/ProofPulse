import { describe, it, expect } from "vitest";
import { execFileSync, execSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { resolve, join } from "node:path";
import { runDafny } from "../backends/dafny/runner.js";
import { RunStatus } from "../backends/backend.js";

const DIST_DIR = resolve(__dirname, "..", "..", "dist", "minimization");
const WRAPPER_JS = join(DIST_DIR, "wrapper.js");
const FIXTURE = resolve(__dirname, "fixtures", "output.smt2.1");
const TRIVIAL_DFY = resolve(__dirname, "fixtures", "trivial.dfy");
// aux$$id2 only supplies the term f(a) that triggers the quantifier of aux$$id1:
// z3's core is (aux$$id1), which does not prove the goal on its own.
const TRIGGER_FIXTURE = resolve(__dirname, "fixtures", "trigger-term-core.smt2");
const TRIGGER_CHAIN_FIXTURE = resolve(__dirname, "fixtures", "trigger-chain.smt2");

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

  for (const mode of ["check", "minimize"]) {
    it(`wrapper in ${mode} mode keeps a fact that only supplies a trigger term`, () => {
      const result = execFileSync("node", [WRAPPER_JS], {
        input: readFileSync(TRIGGER_FIXTURE, "utf-8"),
        encoding: "utf-8",
        timeout: 60_000,
        env: { ...process.env, PROOFPULSE_Z3_PATH: z3Path!, PROOFPULSE_WRAPPER_MODE: mode },
      });
      const core = result.trim().split("\n").pop()!;
      expect(core).toMatch(/aux\$\$id1/);
      expect(core).toMatch(/aux\$\$id2/);
    });
  }

  // z3's core is (aux$$id2); its trigger term f(a) comes from instantiating
  // aux$$id1 on g(a), supplied by aux$$id3. aux$$id4 plays no part.
  for (const mode of ["check", "minimize"]) {
    it(`wrapper in ${mode} mode adds the facts of a trigger chain, and only those`, () => {
      const result = execFileSync("node", [WRAPPER_JS], {
        input: readFileSync(TRIGGER_CHAIN_FIXTURE, "utf-8"),
        encoding: "utf-8",
        timeout: 60_000,
        env: { ...process.env, PROOFPULSE_Z3_PATH: z3Path!, PROOFPULSE_WRAPPER_MODE: mode },
      });
      const core = result.trim().split("\n").pop()!.replace(/[()]/g, "").split(/\s+/).sort();
      expect(core).toEqual(["aux$$id1", "aux$$id2", "aux$$id3"]);
    });
  }

  it.skipIf(!hasDafny)("runDafny with minimization on trivial .dfy completes without error", async () => {
    const result = await runDafny(TRIVIAL_DFY, {
      minimization: {},
      timeoutSeconds: 120,
    });
    expect(result.errorMessage).toBeUndefined();
    expect(result.status).toBe(RunStatus.Completed);
  }, 180_000);
});
