import { spawn } from "node:child_process";
import { existsSync, readdirSync } from "node:fs";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { dirname, join, resolve } from "node:path";
import { tmpdir } from "node:os";
import type { DafnyOptions, DafnyResult } from "./types.js";

const DEFAULT_TIMEOUT_SEC = 60;

/**
 * Resolve the z3 binary bundled inside a Dafny installation.
 * Dafny ships z3 at <dafny_dir>/z3/bin/z3-<version>.
 * Falls back to "z3" on PATH.
 */
function resolveZ3Path(dafnyPath: string): string {
  try {
    // Resolve symlinks / bare names via which-style lookup isn't needed —
    // if dafnyPath is absolute we can find z3 next to it.
    const dafnyDir = dirname(dafnyPath);
    const z3BinDir = join(dafnyDir, "z3", "bin");
    if (existsSync(z3BinDir)) {
      const entries = readdirSync(z3BinDir)
        .filter((f) => f.startsWith("z3"))
        .sort()
        .reverse(); // prefer latest version
      if (entries.length > 0) {
        const candidate = join(z3BinDir, entries[0]);
        if (existsSync(candidate)) return candidate;
      }
    }
  } catch {
    // fall through
  }
  return "z3";
}

export async function runDafny(
  filePath: string,
  options?: DafnyOptions
): Promise<DafnyResult> {
  const dafnyBin = options?.dafnyPath ?? "dafny";
  const timeoutSec = options?.timeoutSeconds ?? DEFAULT_TIMEOUT_SEC;

  // Create temp dir — dafny writes coverage/log artifacts here
  let tmpDir: string;
  try {
    tmpDir = await mkdtemp(join(tmpdir(), "proofpulse-"));
  } catch (err) {
    return { log: "", exitCode: -1, error: `failed to create temp dir: ${(err as Error).message}` };
  }

  const args = [
    "verify",
    filePath,
    "--verification-coverage-report", join(tmpDir, "cov"),
    "--log-format", "text",
    "--isolate-assertions",
    "--allow-warnings", "true",
    "--verification-time-limit", String(timeoutSec),
    "--boogie", "/proverOpt:O:smt.core.minimize=true",
    "--boogie", "/proverOpt:O:sat.core.minimize=true",
  ];

  let spawnEnv: Record<string, string> | undefined;

  if (options?.forceMinimization) {
    // Locate scripts directory (bundled at dist/scripts/)
    const scriptsDir = existsSync(resolve(__dirname, "scripts"))
      ? resolve(__dirname, "scripts")
      : resolve(__dirname, "..", "scripts");
    const wrapperPath = join(scriptsDir, "z3-minimizer-wrapper.sh");

    if (!existsSync(wrapperPath)) {
      return { log: "", exitCode: -1, error: `z3-minimizer-wrapper.sh not found at ${wrapperPath}` };
    }

    const z3Path = resolveZ3Path(dafnyBin);
    const wrapperLog = join(tmpDir, "wrapper.log");

    // --solver-path tells Dafny/Boogie to use our wrapper instead of z3
    args.push("--solver-path", wrapperPath);

    spawnEnv = {
      PROOFPULSE_Z3_PATH: z3Path,
      PROOFPULSE_WRAPPER_LOG: wrapperLog,
    };

    // Log resolved paths for debugging
    const debugInfo = [
      `dafnyBin: ${dafnyBin}`,
      `z3Path: ${z3Path}`,
      `wrapperPath: ${wrapperPath}`,
      `scriptsDir: ${scriptsDir}`,
    ].join("\n");
    await writeFile(join(tmpDir, "debug_info.txt"), debugInfo, "utf8").catch(() => {});
  }

  try {
    const result = await spawnDafny(dafnyBin, args, tmpDir, timeoutSec, spawnEnv);

    // Build debug context for error messages
    let debugContext = "";
    if (options?.forceMinimization) {
      try {
        const wrapperLog = await readFile(join(tmpDir, "wrapper.log"), "utf8").catch(() => "");
        if (wrapperLog) {
          debugContext = `\n--- wrapper log ---\n${wrapperLog.slice(-1000)}`;
        }
      } catch { /* ignore */ }
    }

    if (result.error) {
      return { log: "", exitCode: -1, error: `${result.error}${debugContext}` };
    }

    if (result.timedOut) {
      return { log: "", exitCode: -1, timedOut: true, error: debugContext ? `timed out${debugContext}` : undefined };
    }

    // Non-zero exit with stderr → surface the error
    if (result.exitCode !== 0 && result.stderr) {
      return {
        log: "",
        exitCode: result.exitCode ?? -1,
        error: `dafny exited ${result.exitCode}: ${result.stderr.slice(0, 500)}${debugContext}`,
      };
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
  stderr?: string;
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
          resolve({ exitCode: code ?? -1, stdout, stderr: stderr || undefined });
        }
      }
    });
  });
}
