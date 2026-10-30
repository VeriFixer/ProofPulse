/**
 * Z3 implementation of SolverMinimizer: prepares a launcher that runs
 * `wrapper.js` (an SMT-LIB proxy that minimizes unsat cores) in place of z3.
 * Verifier-independent; each backend wires it in through its MinimizationHook.
 */
import { existsSync } from "node:fs";
import { chmod, writeFile } from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { SolverKind } from "../report/coverage-report.js";
import type { MinimizerCommand, SolverMinimizer } from "../backends/backend.js";
import { IS_WIN, resolveExecutableInPath } from "../util/executables.js";

import { Z3WrapperEnv, Z3WrapperMode } from "./env.js";

export { Z3WrapperEnv, Z3WrapperMode };

// Works in both ESM (import.meta.url) and CJS (esbuild bundle provides __dirname)
const moduleDir = (() => {
  try {
    if (typeof import.meta?.url === "string" && import.meta.url !== "") {
      return dirname(fileURLToPath(import.meta.url));
    }
  } catch { /* fallback */ }
  return typeof (globalThis as any).__dirname === "string"
    ? (globalThis as any).__dirname
    : dirname(typeof __filename === "string" ? __filename : "");
})();

/**
 * Directories wrapper.js and scripts/ are looked up from: this module's own
 * directory (bundles put everything next to the bundle), then its parent
 * (core/dist/minimization → core/dist).
 */
const SEARCH_BASES = [moduleDir, resolve(moduleDir, "..")];

function findScriptsDir(): string {
  for (const base of SEARCH_BASES) {
    for (const candidate of [resolve(base, "scripts"), resolve(base, "..", "scripts")]) {
      if (existsSync(candidate)) return candidate;
    }
  }
  return resolve(moduleDir, "..", "..", "scripts");
}

function wrapperCandidates(scriptsDir: string): string[] {
  const out: string[] = [resolve(moduleDir, "wrapper.js")];
  for (const base of SEARCH_BASES) {
    // core/dist layout, then the VS Code bundle layout (dist/dist/minimization)
    out.push(resolve(base, "minimization", "wrapper.js"));
    out.push(resolve(base, "dist", "minimization", "wrapper.js"));
  }
  out.push(resolve(scriptsDir, "..", "dist", "minimization", "wrapper.js"));
  return out;
}

export class Z3Minimizer implements SolverMinimizer {
  readonly solverKind = SolverKind.Z3;

  async prepare(solverPath: string, logFile: string, tmpDir: string, log: (msg: string) => void): Promise<MinimizerCommand> {
    const scriptsDir = findScriptsDir();
    // On non-Windows, the shell wrapper is the fallback launcher and a sanity
    // check that the scripts directory was bundled correctly.
    const shellWrapper = join(scriptsDir, "z3-minimizer-wrapper.sh");
    if (!IS_WIN && !existsSync(shellWrapper)) {
      throw new Error(`z3-minimizer-wrapper.sh not found at ${shellWrapper}. Ensure the extension was built correctly.`);
    }

    const candidates = wrapperCandidates(scriptsDir);
    const wrapperJs = candidates.find((c) => existsSync(c));
    if (!wrapperJs) {
      throw new Error(`wrapper.js not found. Searched:\n${candidates.map((c) => `  ${c}`).join("\n")}`);
    }

    // process.execPath in VS Code is the Electron binary — it can run JS but
    // behaves differently with interactive stdin/stdout piping (can hang).
    // Prefer a real node binary from PATH; fall back to process.execPath.
    const pathNode = resolveExecutableInPath("node");
    const nodeBin = pathNode ?? process.execPath;
    log(`[info] Node binary for wrapper: ${nodeBin} (source: ${pathNode ? "PATH" : "process.execPath (Electron)"})`);
    log(`[info] Wrapper dist module: ${wrapperJs}`);

    let executable: string;
    if (IS_WIN) {
      const cmdPath = join(tmpDir, "z3-minimizer-wrapper.cmd");
      try {
        await writeFile(cmdPath, `@echo off\r\n"${nodeBin}" --no-warnings "${wrapperJs}" %*\r\n`, "utf8");
      } catch {
        throw new Error(`failed to create wrapper .cmd at ${cmdPath}`);
      }
      executable = cmdPath;
    } else {
      const shimPath = join(tmpDir, "z3-minimizer-wrapper");
      try {
        await writeFile(shimPath, `#!/usr/bin/env sh\nexec "${nodeBin}" --no-warnings "${wrapperJs}" "$@"\n`, "utf8");
        await chmod(shimPath, 0o755);
        executable = shimPath;
      } catch {
        executable = shellWrapper;
      }
    }
    log(`[info] Effective wrapper path: ${executable}`);

    return {
      executable,
      env: {
        [Z3WrapperEnv.SolverPath]: solverPath,
        [Z3WrapperEnv.LogFile]: logFile,
      },
      debugInfo: [`nodeBin: ${nodeBin}`, `distWrapper: ${wrapperJs}`, `effectiveWrapper: ${executable}`],
    };
  }
}
