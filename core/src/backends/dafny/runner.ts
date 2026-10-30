import { spawn } from "node:child_process";
import { existsSync, readdirSync } from "node:fs";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { basename, dirname, isAbsolute, join, resolve } from "node:path";
import { homedir, tmpdir, platform } from "node:os";
import { RunStatus } from "../backend.js";
import type { BackendOptions } from "../backend.js";
import { VerifierId } from "../../report/coverage-report.js";
import { IS_MAC, IS_WIN, isExecutableFile, probeVersion, resolveExecutableInPath } from "../../util/executables.js";
import { Z3Minimizer, Z3WrapperEnv, Z3WrapperMode } from "../../minimization/z3-minimizer.js";
import { DafnyMinimizationHook } from "./minimization-hook.js";
import { assertNever } from "../../util/assert-never.js";

export { probeVersion };

// ---------------------------------------------------------------------------
// Constants & helpers
// ---------------------------------------------------------------------------

/** Command name used when no Dafny path is configured: resolve it automatically. */
export const DEFAULT_DAFNY_COMMAND = "dafny";

const DEFAULT_TIMEOUT_SEC = 60;
const PROVER_LOG_FILE = "prover_log.txt";
const WRAPPER_LOG_FILE = "wrapper.log";
const DEBUG_INFO_FILE = "debug_info.txt";

/** Result of one Dafny run: the raw text log plus how the run ended. */
export interface DafnyRunResult {
  status: RunStatus;
  log: string;
  exitCode: number;
  errorMessage?: string;
  /** `dafny --version` of the binary that ran, when known. */
  dafnyVersion?: string;
}

export interface DafnyRunOptions extends Omit<BackendOptions, "onPreliminaryResult"> {
  /** Called with the unminimized run's result before the minimization run starts. */
  onPreliminaryResult?: (result: DafnyRunResult) => void;
}

const failed = (errorMessage: string, exitCode = -1): DafnyRunResult =>
  ({ status: RunStatus.Failed, log: "", exitCode, errorMessage });

/**
 * On Windows, normalize the file path to have an uppercase drive letter.
 * Dafny's CoverageReporter crashes (IndexOutOfRangeException) when the drive
 * letter casing between the source URI and the report directory differs.
 */
function normalizeFilePath(p: string): string {
  const normalized = resolve(p);
  if (IS_WIN && /^[a-z]:/.test(normalized)) {
    return normalized[0].toUpperCase() + normalized.slice(1);
  }
  return normalized;
}

async function makeTempDir(): Promise<string> {
  let dir = await mkdtemp(join(tmpdir(), "proofpulse-"));
  if (IS_WIN && /^[a-z]:/.test(dir)) {
    dir = dir[0].toUpperCase() + dir.slice(1);
  }
  return dir;
}

function compareVersionLikePaths(left: string, right: string): number {
  return left.localeCompare(right, undefined, { numeric: true, sensitivity: "base" });
}

// ---------------------------------------------------------------------------
// VS Code extension roots
// ---------------------------------------------------------------------------

function getVscodeExtensionsRoots(): string[] {
  const home = process.env.HOME ?? process.env.USERPROFILE ?? homedir();
  if (!home) return [];

  const roots: string[] = [
    join(home, ".vscode", "extensions"),
    join(home, ".vscode-server", "extensions"),
    join(home, ".vscode-remote", "extensions"),
  ];

  // macOS: VS Code also uses ~/Library/Application Support/Code/User/globalStorage
  // but extensions are still in ~/.vscode/extensions. However, VS Code Insiders
  // and Cursor use different directories.
  if (IS_MAC) {
    roots.push(join(home, ".vscode-insiders", "extensions"));
    roots.push(join(home, ".cursor", "extensions"));
  }
  if (IS_WIN) {
    roots.push(join(home, ".vscode-insiders", "extensions"));
    roots.push(join(home, ".cursor", "extensions"));
  }

  return roots.filter((root) => existsSync(root));
}

// ---------------------------------------------------------------------------
// Bundled Dafny resolution
// ---------------------------------------------------------------------------

/**
 * Find the Dafny launcher bundled by the official VS Code extension.
 * Handles platform differences: dafny (Linux/macOS), dafny.exe (Windows).
 */
export function resolveBundledDafnyPath(extensionsRoots = getVscodeExtensionsRoots()): string | undefined {
  const candidates: string[] = [];
  const dafnyNames = IS_WIN ? ["dafny.exe", "Dafny.exe"] : ["dafny", "Dafny"];

  for (const extensionsRoot of extensionsRoots) {
    let extensionEntries: import("node:fs").Dirent[];
    try {
      extensionEntries = readdirSync(extensionsRoot, { withFileTypes: true });
    } catch { continue; }

    for (const extensionEntry of extensionEntries) {
      if (!extensionEntry.isDirectory()) continue;

      const resourcesRoot = join(extensionsRoot, extensionEntry.name, "out", "resources");
      if (!existsSync(resourcesRoot)) continue;

      let resourceEntries: import("node:fs").Dirent[];
      try {
        resourceEntries = readdirSync(resourcesRoot, { withFileTypes: true });
      } catch { continue; }

      for (const resourceEntry of resourceEntries) {
        if (!resourceEntry.isDirectory()) continue;

        for (const name of dafnyNames) {
          const dafnyLauncher = join(resourcesRoot, resourceEntry.name, "github", "dafny", name);
          if (isExecutableFile(dafnyLauncher)) {
            candidates.push(dafnyLauncher);
          }
        }
      }
    }
  }

  if (candidates.length === 0) return undefined;
  candidates.sort(compareVersionLikePaths);
  return candidates[candidates.length - 1];
}

// ---------------------------------------------------------------------------
// Bundled Z3 resolution
// ---------------------------------------------------------------------------

/**
 * Find the Z3 binary bundled by the official VS Code extension.
 */
export function resolveBundledZ3Path(extensionsRoots = getVscodeExtensionsRoots()): string | undefined {
  const candidates: string[] = [];

  for (const extensionsRoot of extensionsRoots) {
    let extensionEntries: import("node:fs").Dirent[];
    try {
      extensionEntries = readdirSync(extensionsRoot, { withFileTypes: true });
    } catch { continue; }

    for (const extensionEntry of extensionEntries) {
      if (!extensionEntry.isDirectory()) continue;

      const resourcesRoot = join(extensionsRoot, extensionEntry.name, "out", "resources");
      if (!existsSync(resourcesRoot)) continue;

      let resourceEntries: import("node:fs").Dirent[];
      try {
        resourceEntries = readdirSync(resourcesRoot, { withFileTypes: true });
      } catch { continue; }

      for (const resourceEntry of resourceEntries) {
        if (!resourceEntry.isDirectory()) continue;

        const z3BinDir = join(resourcesRoot, resourceEntry.name, "github", "dafny", "z3", "bin");
        if (!existsSync(z3BinDir)) continue;

        let z3Entries: import("node:fs").Dirent[];
        try {
          z3Entries = readdirSync(z3BinDir, { withFileTypes: true });
        } catch { continue; }

        for (const z3Entry of z3Entries) {
          if (!z3Entry.isFile()) continue;
          const nameLower = z3Entry.name.toLowerCase();
          const isZ3 = IS_WIN
            ? nameLower.startsWith("z3") && nameLower.endsWith(".exe")
            : nameLower.startsWith("z3");
          if (isZ3) {
            const candidate = join(z3BinDir, z3Entry.name);
            if (isExecutableFile(candidate)) candidates.push(candidate);
          }
        }
      }
    }
  }

  if (candidates.length === 0) return undefined;
  candidates.sort(compareVersionLikePaths);
  return candidates[candidates.length - 1];
}

// ---------------------------------------------------------------------------
// Public resolution API
// ---------------------------------------------------------------------------

export enum ResolveSource {
  Manual = "manual",
  Bundled = "bundled",
  Path = "path",
}

export interface ResolvedPath {
  path: string;
  source: ResolveSource;
}

/**
 * Resolve the Dafny executable.
 * Priority: user override → bundled Dafny extension → PATH.
 */
export function resolveDafnyPathWithSource(dafnyPath: string = DEFAULT_DAFNY_COMMAND): ResolvedPath | undefined {
  if (dafnyPath !== DEFAULT_DAFNY_COMMAND) {
    return { path: dafnyPath, source: ResolveSource.Manual };
  }
  const bundled = resolveBundledDafnyPath();
  if (bundled) return { path: bundled, source: ResolveSource.Bundled };

  const fromPath = resolveExecutableInPath("dafny") || resolveExecutableInPath("Dafny");
  if (fromPath) return { path: fromPath, source: ResolveSource.Path };

  return undefined;
}

/**
 * Resolve the z3 binary.
 * Priority: explicit override → sibling of dafny → bundled extension → PATH.
 */
export function resolveZ3PathWithSource(dafnyPath: string, z3Override?: string): ResolvedPath | undefined {
  if (z3Override) {
    return { path: z3Override, source: ResolveSource.Manual };
  }

  // Sibling z3 of the resolved dafny binary (guaranteed compatible)
  try {
    if (isAbsolute(dafnyPath)) {
      const dafnyDir = dirname(dafnyPath);
      const z3BinDir = join(dafnyDir, "z3", "bin");
      if (existsSync(z3BinDir)) {
        const entries = readdirSync(z3BinDir, { withFileTypes: true })
          .filter((entry) => {
            if (!entry.isFile()) return false;
            const nameLower = entry.name.toLowerCase();
            return IS_WIN
              ? nameLower.startsWith("z3") && nameLower.endsWith(".exe")
              : nameLower.startsWith("z3");
          })
          .map((entry) => entry.name)
          .sort(compareVersionLikePaths);
        if (entries.length > 0) {
          const candidate = join(z3BinDir, entries[entries.length - 1]);
          if (existsSync(candidate)) return { path: candidate, source: ResolveSource.Bundled };
        }
      }
    }
  } catch { /* fall through */ }

  const bundled = resolveBundledZ3Path();
  if (bundled) return { path: bundled, source: ResolveSource.Bundled };

  const pathZ3 = resolveExecutableInPath("z3");
  if (pathZ3) return { path: pathZ3, source: ResolveSource.Path };

  return undefined;
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

/** Resolve the Z3 binary the minimizer forwards to, warning about mismatched installs. */
function resolveMinimizationSolver(
  dafnyBin: string,
  dafnySource: ResolveSource,
  z3Override: string | undefined,
  log: (msg: string) => void,
): { path: string; source: ResolveSource; version?: string } | undefined {
  const z3Result = resolveZ3PathWithSource(dafnyBin, z3Override);
  if (!z3Result) return undefined;
  const z3Path = z3Result.path;
  log(`[info] Z3 resolved: ${z3Path} (source: ${z3Result.source})`);

  const z3Version = probeVersion(z3Path, "--version") ?? probeVersion(z3Path, "-version");
  if (z3Version) {
    log(`[info] Z3 version: ${z3Version}`);
  } else {
    log(`[warn] Could not determine Z3 version — '${z3Path} --version' failed. The binary may not be executable or may be corrupted.`);
  }

  // Warn if dafny and z3 don't come from the same installation
  if (z3Result.source === ResolveSource.Path && dafnySource !== ResolveSource.Path) {
    log(
      `[warn] Z3 resolved from PATH (${z3Path}) but Dafny is from ${dafnySource} (${dafnyBin}). ` +
      `They may be incompatible. Set proofpulse.z3Path to the z3 bundled with your Dafny installation.`
    );
  } else if (z3Result.source === ResolveSource.Manual && dafnySource === ResolveSource.Bundled) {
    if (!z3Path.includes(dirname(dafnyBin))) {
      log(
        `[warn] Z3 (${z3Path}) does not appear to be from the same Dafny installation as ${dafnyBin}. ` +
        `This may cause version incompatibility issues.`
      );
    }
  } else if (dafnySource === ResolveSource.Manual && z3Result.source === ResolveSource.Bundled) {
    if (!z3Path.includes(dirname(dafnyBin))) {
      log(
        `[warn] Dafny was manually set (${dafnyBin}) but Z3 was auto-resolved from a different location (${z3Path}). ` +
        `Set proofpulse.z3Path to the z3 bundled with your Dafny for guaranteed compatibility.`
      );
    }
  }
  return { ...z3Result, version: z3Version };
}

async function readDebugContext(dirs: { wrapperLogDir?: string; debugInfoDir: string }): Promise<string> {
  let debugContext = "";
  if (dirs.wrapperLogDir) {
    const wl = await readFile(join(dirs.wrapperLogDir, WRAPPER_LOG_FILE), "utf8").catch(() => "");
    if (wl) debugContext = `\n--- wrapper log ---\n${wl.slice(-1000)}`;
  }
  const di = await readFile(join(dirs.debugInfoDir, DEBUG_INFO_FILE), "utf8").catch(() => "");
  if (di) debugContext = `${debugContext}\n--- debug_info.txt ---\n${di}`;
  return debugContext;
}

/** Turn a finished spawn into a run result, reading Dafny's prover log on success. */
async function collectResult(result: SpawnResult, runDir: string, debugContext: string): Promise<DafnyRunResult> {
  switch (result.status) {
    case SpawnStatus.Aborted:
      return { status: RunStatus.Aborted, log: "", exitCode: -1 };
    case SpawnStatus.LaunchFailed:
      return failed(`${result.errorMessage}${debugContext}`);
    case SpawnStatus.TimedOut:
      return {
        status: RunStatus.TimedOut,
        log: "",
        exitCode: -1,
        ...(debugContext ? { errorMessage: `timed out${debugContext}` } : {}),
      };
    case SpawnStatus.Exited:
      break;
    default:
      return assertNever(result, "spawn result");
  }

  if (result.exitCode !== 0 && result.stderr) {
    return failed(`dafny exited ${result.exitCode}: ${result.stderr.slice(0, 500)}${debugContext}`, result.exitCode);
  }

  let log = "";
  try {
    log = await readFile(join(runDir, PROVER_LOG_FILE), "utf8");
  } catch {
    log = result.stdout;
  }
  return { status: RunStatus.Completed, log, exitCode: result.exitCode };
}

export async function runDafny(filePath: string, options: DafnyRunOptions = {}): Promise<DafnyRunResult> {
  const log = (msg: string) => options.onWarning?.(msg);
  const dafnyOptions = options.backendOptions?.backend === VerifierId.Dafny ? options.backendOptions : undefined;

  // --- Resolve Dafny ---
  log(`[info] platform=${platform()}, arch=${process.arch}, home=${homedir()}`);
  log(`[info] extension roots searched: ${getVscodeExtensionsRoots().join(", ") || "(none found)"}`);

  const dafnyResult = resolveDafnyPathWithSource(options.toolPath ?? DEFAULT_DAFNY_COMMAND);
  if (!dafnyResult) {
    return failed(
      "Dafny not found in PATH or in the official Dafny VS Code extension bundle. " +
      "Set proofpulse.dafnyPath to the full path of your dafny executable.",
    );
  }
  const dafnyBin = dafnyResult.path;
  const dafnySource = dafnyResult.source;
  log(`[info] Dafny resolved: ${dafnyBin} (source: ${dafnySource})`);

  // Probe dafny version
  const dafnyVersion = probeVersion(dafnyBin, "--version") ?? probeVersion(dafnyBin, "/version");
  if (dafnyVersion) {
    log(`[info] Dafny version: ${dafnyVersion}`);
    const majorMatch = dafnyVersion.match(/^(\d+)\./);
    if (majorMatch && parseInt(majorMatch[1], 10) < 4) {
      return failed(
        `Dafny ${dafnyVersion} is not supported. ProofPulse requires Dafny 4.x or later. ` +
        `Update the Dafny VS Code extension or set proofpulse.dafnyPath to a Dafny 4.x binary.`,
      );
    }
  } else {
    log(`[warn] Could not determine Dafny version — '${dafnyBin} --version' failed. The binary may not be executable or may be corrupted.`);
  }

  const timeoutSec = options.timeoutSeconds ?? DEFAULT_TIMEOUT_SEC;

  let tmpDir: string;
  try {
    tmpDir = await makeTempDir();
  } catch (err) {
    return failed(`failed to create temp dir: ${(err as Error).message}`);
  }

  const normalizedPath = normalizeFilePath(filePath);

  // Dafny 4.x CoverageReporter.HtmlReportForFile splits source by Environment.NewLine
  // (\r\n on Windows). If the file has Unix line endings, the line count mismatches token
  // positions and causes IndexOutOfRangeException. Work around by copying the file to a
  // temp path with normalized line endings (and no spaces in the name).
  let effectivePath = normalizedPath;
  if (IS_WIN || /\s/.test(normalizedPath)) {
    const safeName = basename(normalizedPath).replace(/\s+/g, "_");
    effectivePath = join(tmpDir, safeName);
    let content = await readFile(normalizedPath, "utf-8");
    if (IS_WIN) {
      // Normalize to \r\n so Dafny's CoverageReporter line splitting works correctly
      content = content.replace(/\r\n/g, "\n").replace(/\n/g, "\r\n");
    }
    await writeFile(effectivePath, content, "utf-8");
    log(`[info] Copied source to ${effectivePath} (line-ending normalization=${IS_WIN})`);
  }

  const baseArgs = [
    "verify",
    effectivePath,
    "--verification-coverage-report", join(tmpDir, "cov"),
    "--log-format", "text",
    "--isolate-assertions",
    "--allow-warnings", "true",
    "--verification-time-limit", String(timeoutSec),
    "--boogie", "/proverOpt:O:smt.core.minimize=true",
    "--boogie", "/proverOpt:O:sat.core.minimize=true",
  ];

  if (dafnyOptions?.noAbstractInterpretation) {
    baseArgs.push("--no-abstract-interpretation");
  }

  // Every run spawns the z3 wrapper in place of z3: it makes sure each unsat
  // core proves its goal on its own (z3's core leaves out facts that only
  // supplied a trigger term) and, for the minimization run, minimizes it.
  const solver = resolveMinimizationSolver(
    dafnyBin,
    dafnySource,
    options.minimization?.solver?.path ?? options.solver?.path,
    log,
  );
  if (options.minimization && !solver) {
    return failed(
      "Z3 not found in PATH or in the official Dafny VS Code extension bundle. " +
      "Set proofpulse.z3Path to the full path of your z3 executable.",
    );
  }

  const debugLines: string[] = [];
  const wrapped = async (mode: Z3WrapperMode, logFile: string): Promise<{ args: string[]; env: Record<string, string> }> => {
    const cmd = await new Z3Minimizer().prepare(solver!.path, logFile, tmpDir, log);
    const hooked = new DafnyMinimizationHook().apply(cmd);
    debugLines.push(...cmd.debugInfo);
    return { args: [...baseArgs, ...hooked.args], env: { ...hooked.env, [Z3WrapperEnv.Mode]: mode } };
  };

  // Normal run: the wrapper in check mode; without a z3 to wrap, Dafny's own solver.
  let normal: { args: string[]; env?: Record<string, string> } = {
    args: options.solver?.path ? [...baseArgs, "--solver-path", options.solver.path] : baseArgs,
  };
  if (solver) {
    try {
      normal = await wrapped(Z3WrapperMode.Check, join(tmpDir, WRAPPER_LOG_FILE));
    } catch (err) {
      log(`[warn] z3 wrapper unavailable, cores are not checked: ${(err as Error).message}`);
    }
  } else {
    log("[warn] z3 not found, cores are not checked: facts that only supply trigger terms may show as uncovered");
  }

  // Minimization run: the wrapper in minimize mode.
  let minimization: { args: string[]; env: Record<string, string> } | undefined;
  if (options.minimization) {
    try {
      minimization = await wrapped(Z3WrapperMode.Minimize, options.minimization.logFile ?? join(tmpDir, WRAPPER_LOG_FILE));
    } catch (err) {
      return failed((err as Error).message);
    }
  }

  if (solver) {
    // Persist debug info for post-mortem
    const debugInfo = [
      `platform: ${platform()}`,
      `dafnyBin: ${dafnyBin} (source: ${dafnySource})`,
      `dafnyVersion: ${dafnyVersion ?? "unknown"}`,
      `z3Path: ${solver.path} (source: ${solver.source})`,
      `z3Version: ${solver.version ?? "unknown"}`,
      ...debugLines,
    ].join("\n");
    await writeFile(join(tmpDir, DEBUG_INFO_FILE), debugInfo, "utf8").catch(() => {});
  }

  const withVersion = (r: DafnyRunResult): DafnyRunResult => (dafnyVersion ? { ...r, dafnyVersion } : r);

  try {
    // Two-phase progressive run: Phase_1 (normal) → callback → Phase_2 (minimization)
    if (minimization && options.onPreliminaryResult) {
      log(`[info] Phase_1 (normal): ${dafnyBin} ${normal.args.join(" ")}`);
      const phase1 = await spawnDafny(dafnyBin, normal.args, tmpDir, timeoutSec, normal.env, options.signal);
      // Phase 1 errors are reported without minimization debug context.
      const phase1Result = await collectResult(phase1, tmpDir, "");
      if (phase1Result.status !== RunStatus.Completed) {
        return { ...phase1Result, errorMessage: phase1Result.status === RunStatus.TimedOut ? undefined : phase1Result.errorMessage };
      }
      options.onPreliminaryResult(withVersion(phase1Result));

      // Check abort between phases
      if (options.signal?.aborted) {
        return { status: RunStatus.Aborted, log: "", exitCode: -1 };
      }

      // Phase_2: minimization run in a fresh tmpDir
      let tmpDir2: string;
      try {
        tmpDir2 = await makeTempDir();
      } catch (err) {
        return failed(`failed to create temp dir for phase2: ${(err as Error).message}`);
      }

      log(`[info] Phase_2 (minimization): ${dafnyBin} ${minimization.args.join(" ")}`);
      try {
        const phase2 = await spawnDafny(dafnyBin, minimization.args, tmpDir2, timeoutSec, minimization.env, options.signal);
        const debugContext = await readDebugContext({ wrapperLogDir: tmpDir2, debugInfoDir: tmpDir });
        return withVersion(await collectResult(phase2, tmpDir2, debugContext));
      } finally {
        rm(tmpDir2, { recursive: true, force: true }).catch(() => {});
      }
    }

    // Single-phase run (minimized when configured)
    const run = minimization ?? normal;
    log(`[info] Spawning: ${dafnyBin} ${run.args.join(" ")}`);
    const result = await spawnDafny(dafnyBin, run.args, tmpDir, timeoutSec, run.env, options.signal);
    const debugContext = await readDebugContext({ wrapperLogDir: run.env ? tmpDir : undefined, debugInfoDir: tmpDir });
    return withVersion(await collectResult(result, tmpDir, debugContext));
  } finally {
    rm(tmpDir, { recursive: true, force: true }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// Spawn helper
// ---------------------------------------------------------------------------

enum SpawnStatus {
  Exited = "exited",
  TimedOut = "timedOut",
  Aborted = "aborted",
  LaunchFailed = "launchFailed",
}

type SpawnResult =
  | { status: SpawnStatus.Exited; exitCode: number; stdout: string; stderr?: string }
  | { status: SpawnStatus.TimedOut }
  | { status: SpawnStatus.Aborted }
  | { status: SpawnStatus.LaunchFailed; errorMessage: string };

function spawnDafny(
  bin: string,
  args: string[],
  cwd: string,
  timeoutSec: number,
  extraEnv?: Record<string, string>,
  signal?: AbortSignal
): Promise<SpawnResult> {
  if (signal?.aborted) {
    return Promise.resolve({ status: SpawnStatus.Aborted });
  }

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

    // Resolve as soon as the run is aborted: a killed launcher's children can
    // keep the output pipes open, so waiting for "close" may take until they exit.
    signal?.addEventListener("abort", () => {
      child.kill("SIGKILL");
      clearTimeout(timer);
      if (!done) {
        done = true;
        resolve({ status: SpawnStatus.Aborted });
      }
    }, { once: true });

    child.stdout?.on("data", (d: Buffer) => { stdout += d.toString(); });
    child.stderr?.on("data", (d: Buffer) => { stderr += d.toString(); });

    child.on("error", (err: Error) => {
      clearTimeout(timer);
      if (!done) {
        done = true;
        const msg = err.message?.includes("ENOENT") ? `binary not found: ${bin}` : err.message;
        resolve({ status: SpawnStatus.LaunchFailed, errorMessage: msg });
      }
    });

    child.on("close", (code: number | null) => {
      clearTimeout(timer);
      if (!done) {
        done = true;
        if (signal?.aborted) {
          resolve({ status: SpawnStatus.Aborted });
        } else if (timedOut) {
          resolve({ status: SpawnStatus.TimedOut });
        } else {
          resolve({ status: SpawnStatus.Exited, exitCode: code ?? -1, stdout, stderr: stderr || undefined });
        }
      }
    });
  });
}
