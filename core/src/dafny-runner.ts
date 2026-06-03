import { spawn, execFileSync } from "node:child_process";
import { accessSync, constants as fsConstants, existsSync, readdirSync } from "node:fs";
import { mkdtemp, readFile, rm, writeFile, chmod } from "node:fs/promises";
import { basename, delimiter, dirname, isAbsolute, join, resolve } from "node:path";
import { homedir, tmpdir, platform } from "node:os";
import { fileURLToPath } from "node:url";
import type { DafnyOptions, DafnyResult } from "./types.js";

// ---------------------------------------------------------------------------
// Constants & helpers
// ---------------------------------------------------------------------------

// Works in both ESM (import.meta.url) and CJS (esbuild bundle provides __dirname)
const __dirname = (() => {
  try {
    if (typeof import.meta?.url === "string" && import.meta.url !== "") {
      return dirname(fileURLToPath(import.meta.url));
    }
  } catch { /* fallback */ }
  // CJS fallback — esbuild injects __dirname in CJS output
  return typeof (globalThis as any).__dirname === "string"
    ? (globalThis as any).__dirname
    : dirname(typeof __filename === "string" ? __filename : "");
})();

const DEFAULT_TIMEOUT_SEC = 60;
const IS_WIN = platform() === "win32";
const IS_MAC = platform() === "darwin";

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

function isExecutableFile(filePath: string): boolean {
  if (!existsSync(filePath)) return false;
  if (IS_WIN) return true;
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
  const suffixes = IS_WIN ? ["", ".exe", ".cmd", ".bat"] : [""];

  for (const pathEntry of pathEnv.split(delimiter)) {
    if (!pathEntry) continue;
    for (const suffix of suffixes) {
      const candidate = join(pathEntry, executableName + suffix);
      if (isExecutableFile(candidate)) return candidate;
    }
  }
  return undefined;
}

/**
 * Run a binary with a single arg (like --version / -version) and return stdout.
 * Returns undefined on failure. Timeout: 5s.
 */
function probeVersion(bin: string, arg: string): string | undefined {
  try {
    const out = execFileSync(bin, [arg], { encoding: "utf-8", timeout: 5000, stdio: ["ignore", "pipe", "pipe"] });
    return out.trim().split("\n")[0];
  } catch {
    return undefined;
  }
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

export type ResolveSource = "manual" | "bundled" | "path";

export interface ResolvedPath {
  path: string;
  source: ResolveSource;
}

/**
 * Resolve the Dafny executable.
 * Priority: user override → bundled Dafny extension → PATH.
 */
export function resolveDafnyPathWithSource(dafnyPath: string): ResolvedPath | undefined {
  if (dafnyPath !== "dafny") {
    return { path: dafnyPath, source: "manual" };
  }
  const bundled = resolveBundledDafnyPath();
  if (bundled) return { path: bundled, source: "bundled" };

  const fromPath = resolveExecutableInPath("dafny") || resolveExecutableInPath("Dafny");
  if (fromPath) return { path: fromPath, source: "path" };

  return undefined;
}

/**
 * Resolve the z3 binary.
 * Priority: explicit override → sibling of dafny → bundled extension → PATH.
 */
export function resolveZ3PathWithSource(dafnyPath: string, z3Override?: string): { path: string; source: ResolveSource } | undefined {
  if (z3Override) {
    return { path: z3Override, source: "manual" };
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
          if (existsSync(candidate)) return { path: candidate, source: "bundled" };
        }
      }
    }
  } catch { /* fall through */ }

  const bundled = resolveBundledZ3Path();
  if (bundled) return { path: bundled, source: "bundled" };

  const pathZ3 = resolveExecutableInPath("z3");
  if (pathZ3) return { path: pathZ3, source: "path" };

  return undefined;
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

export async function runDafny(
  filePath: string,
  options?: DafnyOptions
): Promise<DafnyResult> {
  const log = (msg: string) => options?.onWarning?.(msg);

  // --- Resolve Dafny ---
  log(`[info] platform=${platform()}, arch=${process.arch}, home=${homedir()}`);
  log(`[info] extension roots searched: ${getVscodeExtensionsRoots().join(", ") || "(none found)"}`);

  const dafnyResult = resolveDafnyPathWithSource(options?.dafnyPath ?? "dafny");
  if (!dafnyResult) {
    return {
      log: "",
      exitCode: -1,
      error: "Dafny not found in PATH or in the official Dafny VS Code extension bundle. " +
        "Set proofpulse.dafnyPath to the full path of your dafny executable.",
    };
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
      return {
        log: "",
        exitCode: -1,
        error: `Dafny ${dafnyVersion} is not supported. ProofPulse requires Dafny 4.x or later. ` +
          `Update the Dafny VS Code extension or set proofpulse.dafnyPath to a Dafny 4.x binary.`,
      };
    }
  } else {
    log(`[warn] Could not determine Dafny version — '${dafnyBin} --version' failed. The binary may not be executable or may be corrupted.`);
  }

  const timeoutSec = options?.timeoutSeconds ?? DEFAULT_TIMEOUT_SEC;

  // Create temp dir
  let tmpDir: string;
  try {
    tmpDir = await mkdtemp(join(tmpdir(), "proofpulse-"));
    if (IS_WIN && /^[a-z]:/.test(tmpDir)) {
      tmpDir = tmpDir[0].toUpperCase() + tmpDir.slice(1);
    }
  } catch (err) {
    return { log: "", exitCode: -1, error: `failed to create temp dir: ${(err as Error).message}` };
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

  const args = [
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

  if (options?.noAbstractInterpretation) {
    args.push("--no-abstract-interpretation");
  }

  let spawnEnv: Record<string, string> | undefined;

  if (options?.forceMinimization) {
    // Locate scripts directory (bundled at dist/scripts/)
    const scriptsDir = existsSync(resolve(__dirname, "scripts"))
      ? resolve(__dirname, "scripts")
      : resolve(__dirname, "..", "scripts");
    // On non-Windows, verify the shell wrapper exists (used as a sanity check
    // that the scripts directory was bundled correctly).
    const wrapperPath = join(scriptsDir, "z3-minimizer-wrapper.sh");
    if (!IS_WIN && !existsSync(wrapperPath)) {
      return { log: "", exitCode: -1, error: `z3-minimizer-wrapper.sh not found at ${wrapperPath}. Ensure the extension was built correctly.` };
    }

    // --- Resolve Z3 ---
    const z3Result = resolveZ3PathWithSource(dafnyBin, options?.z3Path);
    if (!z3Result) {
      return { log: "", exitCode: -1, error: "Z3 not found in PATH or in the official Dafny VS Code extension bundle. " +
        "Set proofpulse.z3Path to the full path of your z3 executable." };
    }
    const z3Path = z3Result.path;
    log(`[info] Z3 resolved: ${z3Path} (source: ${z3Result.source})`);

    // Probe z3 version
    const z3Version = probeVersion(z3Path, "--version") ?? probeVersion(z3Path, "-version");
    if (z3Version) {
      log(`[info] Z3 version: ${z3Version}`);
    } else {
      log(`[warn] Could not determine Z3 version — '${z3Path} --version' failed. The binary may not be executable or may be corrupted.`);
    }

    // Warn if dafny and z3 don't come from the same installation
    if (z3Result.source === "path" && dafnySource !== "path") {
      log(
        `[warn] Z3 resolved from PATH (${z3Path}) but Dafny is from ${dafnySource} (${dafnyBin}). ` +
        `They may be incompatible. Set proofpulse.z3Path to the z3 bundled with your Dafny installation.`
      );
    } else if (z3Result.source === "manual" && dafnySource === "bundled") {
      if (!z3Path.includes(dirname(dafnyBin))) {
        log(
          `[warn] Z3 (${z3Path}) does not appear to be from the same Dafny installation as ${dafnyBin}. ` +
          `This may cause version incompatibility issues.`
        );
      }
    } else if (dafnySource === "manual" && z3Result.source === "bundled") {
      if (!z3Path.includes(dirname(dafnyBin))) {
        log(
          `[warn] Dafny was manually set (${dafnyBin}) but Z3 was auto-resolved from a different location (${z3Path}). ` +
          `Set proofpulse.z3Path to the z3 bundled with your Dafny for guaranteed compatibility.`
        );
      }
    }

    const wrapperLog = join(tmpDir, "wrapper.log");

    // Build a platform-appropriate wrapper that Dafny/Boogie can spawn as --solver-path.
    let effectiveWrapperPath: string;

    const distWrapper = resolve(
      // When running from core/dist/ directly (tests, CLI)
      existsSync(resolve(__dirname, "minimization", "wrapper.js"))
        ? resolve(__dirname, "minimization", "wrapper.js")
        // When bundled in vscode extension: dist/dist/minimization/wrapper.js
        : existsSync(resolve(__dirname, "dist", "minimization", "wrapper.js"))
          ? resolve(__dirname, "dist", "minimization", "wrapper.js")
          // Fallback: relative to scripts dir (matches old .sh layout)
          : resolve(scriptsDir, "..", "dist", "minimization", "wrapper.js")
    );

    if (!existsSync(distWrapper)) {
      return { log: "", exitCode: -1, error: `wrapper.js not found. Searched:\n` +
        `  ${resolve(__dirname, "minimization", "wrapper.js")}\n` +
        `  ${resolve(__dirname, "dist", "minimization", "wrapper.js")}\n` +
        `  ${resolve(scriptsDir, "..", "dist", "minimization", "wrapper.js")}` };
    }

    // Find a suitable node binary for the wrapper.
    // process.execPath in VS Code is the Electron binary — it can run JS but
    // behaves differently with interactive stdin/stdout piping (can hang).
    // Prefer a real node binary from PATH; fall back to process.execPath.
    const pathNode = resolveExecutableInPath("node");
    const nodeBin = pathNode ?? process.execPath;
    const nodeSource = pathNode ? "PATH" : "process.execPath (Electron)";
    log(`[info] Node binary for wrapper: ${nodeBin} (source: ${nodeSource})`);
    log(`[info] Wrapper dist module: ${distWrapper}`);

    if (IS_WIN) {
      const cmdPath = join(tmpDir, "z3-minimizer-wrapper.cmd");
      const cmdContents = `@echo off\r\n"${nodeBin}" --no-warnings "${distWrapper}" %*\r\n`;
      try {
        await writeFile(cmdPath, cmdContents, "utf8");
        effectiveWrapperPath = cmdPath;
      } catch {
        return { log: "", exitCode: -1, error: `failed to create wrapper .cmd at ${cmdPath}` };
      }
    } else {
      const shimPath = join(tmpDir, "z3-minimizer-wrapper");
      const shimContents = `#!/usr/bin/env sh\nexec "${nodeBin}" --no-warnings "${distWrapper}" "$@"\n`;
      try {
        await writeFile(shimPath, shimContents, "utf8");
        await chmod(shimPath, 0o755);
        effectiveWrapperPath = shimPath;
      } catch {
        effectiveWrapperPath = wrapperPath;
      }
    }

    log(`[info] Effective wrapper path: ${effectiveWrapperPath}`);
    args.push("--solver-path", effectiveWrapperPath);

    spawnEnv = {
      PROOFPULSE_Z3_PATH: z3Path,
      PROOFPULSE_WRAPPER_LOG: wrapperLog,
    };

    // Persist debug info for post-mortem
    const debugInfo = [
      `platform: ${platform()}`,
      `dafnyBin: ${dafnyBin} (source: ${dafnySource})`,
      `dafnyVersion: ${dafnyVersion ?? "unknown"}`,
      `z3Path: ${z3Path} (source: ${z3Result.source})`,
      `z3Version: ${z3Version ?? "unknown"}`,
      `nodeBin: ${nodeBin}`,
      `distWrapper: ${distWrapper}`,
      `effectiveWrapper: ${effectiveWrapperPath}`,
    ].join("\n");
    await writeFile(join(tmpDir, "debug_info.txt"), debugInfo, "utf8").catch(() => {});
  }

  log(`[info] Spawning: ${dafnyBin} ${args.join(" ")}`);

  try {
    const result = await spawnDafny(dafnyBin, args, tmpDir, timeoutSec, spawnEnv);

    // Build debug context for error messages
    let debugContext = "";
    if (options?.forceMinimization) {
      try {
        const wl = await readFile(join(tmpDir, "wrapper.log"), "utf8").catch(() => "");
        if (wl) debugContext = `\n--- wrapper log ---\n${wl.slice(-1000)}`;
      } catch { /* ignore */ }
    }
    try {
      const di = await readFile(join(tmpDir, "debug_info.txt"), "utf8").catch(() => "");
      if (di) debugContext = `${debugContext}\n--- debug_info.txt ---\n${di}`;
    } catch { /* ignore */ }

    if (result.error) {
      return { log: "", exitCode: -1, error: `${result.error}${debugContext}` };
    }

    if (result.timedOut) {
      return { log: "", exitCode: -1, timedOut: true, error: debugContext ? `timed out${debugContext}` : undefined };
    }

    if (result.exitCode !== 0 && result.stderr) {
      return {
        log: "",
        exitCode: result.exitCode ?? -1,
        error: `dafny exited ${result.exitCode}: ${result.stderr.slice(0, 500)}${debugContext}`,
      };
    }

    // Read prover_log.txt produced by dafny
    let logContent = "";
    try {
      logContent = await readFile(join(tmpDir, "prover_log.txt"), "utf8");
    } catch {
      logContent = result.stdout ?? "";
    }

    return { log: logContent, exitCode: result.exitCode ?? -1, timedOut: false };
  } finally {
    rm(tmpDir, { recursive: true, force: true }).catch(() => {});
  }
}

// ---------------------------------------------------------------------------
// Spawn helper
// ---------------------------------------------------------------------------

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
        const msg = err.message?.includes("ENOENT") ? `binary not found: ${bin}` : err.message;
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
