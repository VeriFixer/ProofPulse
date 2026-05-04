import { spawn } from "node:child_process";
import { accessSync, constants as fsConstants, existsSync, readdirSync } from "node:fs";
import { mkdtemp, readFile, rm, writeFile, chmod } from "node:fs/promises";
import { delimiter, dirname, isAbsolute, join, resolve } from "node:path";
import { tmpdir } from "node:os";
import type { DafnyOptions, DafnyResult } from "./types.js";

const DEFAULT_TIMEOUT_SEC = 60;

function isExecutableFile(filePath: string): boolean {
  if (!existsSync(filePath)) {
    return false;
  }

  if (process.platform === "win32") {
    return true;
  }

  try {
    accessSync(filePath, fsConstants.X_OK);
    return true;
  } catch {
    return false;
  }
}

function compareVersionLikePaths(left: string, right: string): number {
  return left.localeCompare(right, undefined, { numeric: true, sensitivity: "base" });
}

function resolveExecutableInPath(executableName: string): string | undefined {
  const pathEnv = process.env.PATH ?? "";

  for (const pathEntry of pathEnv.split(delimiter)) {
    if (!pathEntry) {
      continue;
    }

    const candidate = join(pathEntry, executableName);
    if (isExecutableFile(candidate)) {
      return candidate;
    }
  }

  return undefined;
}

function getVscodeExtensionsRoots(): string[] {
  const homeDir = process.env.HOME ?? process.env.USERPROFILE;
  if (!homeDir) {
    return [];
  }

  return [
    join(homeDir, ".vscode", "extensions"),
    join(homeDir, ".vscode-server", "extensions"),
    join(homeDir, ".vscode-remote", "extensions"),
  ].filter((root) => existsSync(root));
}

/**
 * Find the Dafny launcher bundled by the official VS Code extension.
 * On Linux this is typically under ~/.vscode/extensions/<ext>/out/resources/<ver>/github/dafny/dafny.
 */
export function resolveBundledDafnyPath(extensionsRoots = getVscodeExtensionsRoots()): string | undefined {
  const candidates: string[] = [];

  for (const extensionsRoot of extensionsRoots) {
    for (const extensionEntry of readdirSync(extensionsRoot, { withFileTypes: true })) {
      if (!extensionEntry.isDirectory()) {
        continue;
      }

      const resourcesRoot = join(extensionsRoot, extensionEntry.name, "out", "resources");
      if (!existsSync(resourcesRoot)) {
        continue;
      }

      for (const resourceEntry of readdirSync(resourcesRoot, { withFileTypes: true })) {
        if (!resourceEntry.isDirectory()) {
          continue;
        }

        const dafnyLauncher = join(resourcesRoot, resourceEntry.name, "github", "dafny", "dafny");
        if (isExecutableFile(dafnyLauncher)) {
          candidates.push(dafnyLauncher);
        }
      }
    }
  }

  if (candidates.length === 0) {
    return undefined;
  }

  candidates.sort(compareVersionLikePaths);
  return candidates[candidates.length - 1];
}

/**
 * Find the Z3 binary bundled by the official VS Code extension.
 * The official Dafny extension stores Z3 under <extension>/out/resources/<ver>/github/dafny/z3/bin/z3-<version>.
 */
export function resolveBundledZ3Path(extensionsRoots = getVscodeExtensionsRoots()): string | undefined {
  const candidates: string[] = [];

  for (const extensionsRoot of extensionsRoots) {
    for (const extensionEntry of readdirSync(extensionsRoot, { withFileTypes: true })) {
      if (!extensionEntry.isDirectory()) {
        continue;
      }

      const resourcesRoot = join(extensionsRoot, extensionEntry.name, "out", "resources");
      if (!existsSync(resourcesRoot)) {
        continue;
      }

      for (const resourceEntry of readdirSync(resourcesRoot, { withFileTypes: true })) {
        if (!resourceEntry.isDirectory()) {
          continue;
        }

        const z3BinDir = join(resourcesRoot, resourceEntry.name, "github", "dafny", "z3", "bin");
        if (!existsSync(z3BinDir)) {
          continue;
        }

        for (const z3Entry of readdirSync(z3BinDir, { withFileTypes: true })) {
          if (!z3Entry.isFile()) {
            continue;
          }

          const candidate = join(z3BinDir, z3Entry.name);
          if (z3Entry.name.startsWith("z3") && isExecutableFile(candidate)) {
            candidates.push(candidate);
          }
        }
      }
    }
  }

  if (candidates.length === 0) {
    return undefined;
  }

  candidates.sort(compareVersionLikePaths);
  return candidates[candidates.length - 1];
}

/**
 * Resolve the Dafny executable used for analysis.
 * If the user left the default "dafny" value, we first try PATH and then the bundled launcher from
 * the official Dafny VS Code extension.
 */
export function resolveDafnyPath(dafnyPath: string): string | undefined {
  if (dafnyPath !== "dafny") {
    return dafnyPath;
  }

  return resolveExecutableInPath("dafny") ?? resolveBundledDafnyPath();
}

/**
 * Resolve the z3 binary bundled inside a Dafny installation.
 * Resolve order: PATH first, then next to an absolute Dafny install, then the bundled extension.
 */
export function resolveZ3Path(dafnyPath: string): string | undefined {
  const pathZ3 = resolveExecutableInPath("z3");
  if (pathZ3) {
    return pathZ3;
  }

  try {
    if (!isAbsolute(dafnyPath)) {
      return resolveBundledZ3Path();
    }

    const dafnyDir = dirname(dafnyPath);
    const z3BinDir = join(dafnyDir, "z3", "bin");
    if (existsSync(z3BinDir)) {
      const entries = readdirSync(z3BinDir, { withFileTypes: true })
        .filter((entry) => entry.isFile() && entry.name.startsWith("z3"))
        .map((entry) => entry.name)
        .sort(compareVersionLikePaths);
      if (entries.length > 0) {
        const candidate = join(z3BinDir, entries[entries.length - 1]);
        if (existsSync(candidate)) return candidate;
      }
    }
  } catch {
    // fall through
  }

  return resolveBundledZ3Path();
}

export async function runDafny(
  filePath: string,
  options?: DafnyOptions
): Promise<DafnyResult> {
  const dafnyBin = resolveDafnyPath(options?.dafnyPath ?? "dafny");
  if (!dafnyBin) {
    return {
      log: "",
      exitCode: -1,
      error: "Dafny not found in PATH or in the official Dafny VS Code extension bundle",
    };
  }
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

    const pythonBin = options?.pythonPath ?? "python";
    const z3Path = resolveZ3Path(dafnyBin);
    if (!z3Path) {
      return { log: "", exitCode: -1, error: "Z3 not found in PATH or in the official Dafny VS Code extension bundle" };
    }
    const wrapperLog = join(tmpDir, "wrapper.log");

    // Ensure wrapper is executable. If the bundled .sh lost exec bit (packaging),
    // create a temporary shim that invokes the Python wrapper directly.
    let effectiveWrapperPath = wrapperPath;
    if (!isExecutableFile(wrapperPath)) {
      // Try to find the python wrapper next to the .sh file
      const wrapperPy = join(scriptsDir, "z3-minimizer-wrapper.py");
      if (existsSync(wrapperPy)) {
        const shimPath = join(tmpDir, "z3-minimizer-wrapper");
        const shimContents = `#!/usr/bin/env sh\nexec \"${pythonBin}\" \"${wrapperPy}\" \"$@\"\n`;
        try {
          await writeFile(shimPath, shimContents, "utf8");
          await chmod(shimPath, 0o755);
          effectiveWrapperPath = shimPath;
        } catch {
          // fallback to bundled .sh even if not executable; let spawn errors surface
          effectiveWrapperPath = wrapperPath;
        }
      }
    }

    // --solver-path tells Dafny/Boogie to use our wrapper instead of z3
    args.push("--solver-path", effectiveWrapperPath);

    spawnEnv = {
      PROOFPULSE_Z3_PATH: z3Path,
      PROOFPULSE_PYTHON_PATH: pythonBin,
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

    // Also include debug_info.txt if present
    try {
      const debugInfoFile = await readFile(join(tmpDir, "debug_info.txt"), "utf8").catch(() => "");
      if (debugInfoFile) {
        debugContext = `${debugContext}\n--- debug_info.txt ---\n${debugInfoFile}`;
      }
    } catch { /* ignore */ }

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
