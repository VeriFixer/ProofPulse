import { spawn } from "node:child_process";
import { existsSync } from "node:fs";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { join, resolve } from "node:path";
import { tmpdir } from "node:os";
import type { DafnyOptions, DafnyResult } from "./types.js";

const DEFAULT_TIMEOUT_SEC = 60;

export async function runDafny(
  filePath: string,
  options?: DafnyOptions
): Promise<DafnyResult> {
  const dafnyBin = options?.dafnyPath ?? "dafny";
  const timeoutSec = options?.timeoutSeconds ?? DEFAULT_TIMEOUT_SEC;

  // Create temp dir, we run dafny there so coverage/log artifacts stay isolated
  let tmpDir: string;
  try {
    tmpDir = await mkdtemp(join(tmpdir(), "proofpulse-"));
  } catch (err) {
    return { log: "", exitCode: -1, error: `failed to create temp dir: ${(err as Error).message}` };
  }

  let boogieValue =
    "/proverOpt:O:smt.core.minimize=true /proverOpt:O:sat.core.minimize=true /proverOpt:C:proof=true";

  let spawnEnv: Record<string, string> | undefined;

  if (options?.forceMinimization) {
    // When bundled: extension.js (__dirname=dist/) or server.js (__dirname=dist/web_viewer/)
    // Scripts live at dist/scripts/ — try sibling first, then parent
    const scriptsDir = existsSync(resolve(__dirname, 'scripts'))
      ? resolve(__dirname, 'scripts')
      : resolve(__dirname, '..', 'scripts');
    const wrapperPath = join(scriptsDir, 'z3-minimizer-wrapper.sh');
    const minimizerPath = join(scriptsDir, 'minimize_unsat_core_trace.py');

    if (!existsSync(wrapperPath)) {
      return { log: "", exitCode: -1, error: `z3-minimizer-wrapper.sh not found at ${wrapperPath}` };
    }

    boogieValue += ` /z3exe:${wrapperPath}`;
    spawnEnv = {
      PROOFPULSE_Z3_PATH: options.dafnyPath ?? "z3",
      PROOFPULSE_MINIMIZER_SCRIPT: minimizerPath,
    };
  }

  const args = [
    "verify",
    filePath,
    "--verification-coverage-report", join(tmpDir, "cov"),
    "--log-format", "text",
    "--isolate-assertions",
    "--allow-warnings", "true",
    "--verification-time-limit", String(timeoutSec),
    "--boogie",
    boogieValue,
  ];

  try {
    const result = await spawnDafny(dafnyBin, args, tmpDir, timeoutSec, spawnEnv);

    if (result.error) {
      return { log: "", exitCode: -1, error: result.error };
    }

    if (result.timedOut) {
      return { log: "", exitCode: -1, timedOut: true };
    }

    // Read prover_log.txt produced by dafny
    let log = "";
    try {
      log = await readFile(join(tmpDir, "prover_log.txt"), "utf8");
    } catch {
      // dafny may not produce log on all runs; fall back to stdout
      log = result.stdout ?? "";
    }

    return { log, exitCode: result.exitCode ?? -1, timedOut: false };
  } finally {
    rm(tmpDir, { recursive: true, force: true }).catch(() => {});
  }
}

interface SpawnResult {
  exitCode?: number;
  stdout?: string;
  timedOut?: boolean;
  error?: string;
}

function spawnDafny(
  bin: string,
  args: string[],
  cwd: string,
  timeoutSec: number,
  extraEnv?: Record<string, string>
): Promise<SpawnResult> {
  return new Promise((resolve) => {
    let stdout = "";
    let stderr = "";
    let done = false;

    const env = extraEnv ? { ...process.env, ...extraEnv } : undefined;
    const child = spawn(bin, args, { cwd, env });

    let timedOut = false;
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill("SIGKILL");
    }, timeoutSec * 1000);

    child.stdout?.on("data", (d: Buffer) => { stdout += d.toString(); });
    child.stderr?.on("data", (d: Buffer) => { stderr += d.toString(); });

    child.on("error", (err: Error) => {
      clearTimeout(timer);
      if (!done) {
        done = true;
        const msg = err.message?.includes("ENOENT") ? "dafny not found" : err.message;
        resolve({ error: msg });
      }
    });

    child.on("close", (code: number | null) => {
      clearTimeout(timer);
      if (!done) {
        done = true;
        if (timedOut) {
          resolve({ timedOut: true });
        } else {
          resolve({ exitCode: code ?? -1, stdout });
        }
      }
    });
  });
}
