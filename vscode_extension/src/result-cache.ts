import * as crypto from "node:crypto";
import * as fs from "node:fs/promises";
import * as path from "node:path";
import * as os from "node:os";

export interface CachedResult {
  source: string;
  log: string;
  minimized: boolean;
  timestamp: number;
  filePath: string;
}

const CACHE_DIR = path.join(os.homedir(), ".proofpulse", "cache");

function fileHash(filePath: string): string {
  const absolute = path.resolve(filePath);
  return crypto.createHash("sha256").update(absolute).digest("hex");
}

/** Cache path: {minimized|normal}_{filename}_{hash}.json */
export function getCachePath(filePath: string, minimized: boolean): string {
  const hash = fileHash(filePath);
  const basename = path.basename(filePath);
  const prefix = minimized ? "minimized" : "normal";
  return path.join(CACHE_DIR, `${prefix}_${basename}_${hash}.json`);
}

/** Command file sibling: {minimized|normal}_{filename}_{hash}.cmd.sh */
function getCmdPath(filePath: string, minimized: boolean): string {
  const hash = fileHash(filePath);
  const basename = path.basename(filePath);
  const prefix = minimized ? "minimized" : "normal";
  return path.join(CACHE_DIR, `${prefix}_${basename}_${hash}.cmd.sh`);
}

/** Delete all cached files (both minimized and normal) for a given source file. */
export async function invalidateCache(filePath: string): Promise<void> {
  const hash = fileHash(filePath);
  const basename = path.basename(filePath);
  const targets = [
    `minimized_${basename}_${hash}.json`,
    `minimized_${basename}_${hash}.json.tmp`,
    `minimized_${basename}_${hash}.cmd.sh`,
    `normal_${basename}_${hash}.json`,
    `normal_${basename}_${hash}.json.tmp`,
    `normal_${basename}_${hash}.cmd.sh`,
  ];
  await Promise.all(
    targets.map((name) => fs.rm(path.join(CACHE_DIR, name), { force: true }).catch(() => {}))
  );
}

export async function writeCache(
  filePath: string,
  source: string,
  log: string,
  minimized: boolean,
  command?: string
): Promise<void> {
  const cachePath = getCachePath(filePath, minimized);
  const data: CachedResult = {
    source,
    log,
    minimized,
    timestamp: Date.now(),
    filePath,
  };
  await fs.mkdir(path.dirname(cachePath), { recursive: true });
  const tmp = cachePath + ".tmp";
  await fs.writeFile(tmp, JSON.stringify(data), "utf8");
  await fs.rename(tmp, cachePath);

  // Write command file for local retry
  if (command) {
    const cmdPath = getCmdPath(filePath, minimized);
    await fs.writeFile(cmdPath, `#!/bin/sh\n# Retry command for ${path.basename(filePath)} (${minimized ? "minimized" : "normal"})\n${command}\n`, "utf8").catch(() => {});
  }
}

/**
 * Read cache for a file. Checks minimized first, then normal.
 * Returns null on miss/corrupt.
 */
export async function readCache(filePath: string): Promise<CachedResult | null> {
  // Try minimized first
  try {
    const raw = await fs.readFile(getCachePath(filePath, true), "utf8");
    return JSON.parse(raw) as CachedResult;
  } catch { /* miss */ }
  // Try normal
  try {
    const raw = await fs.readFile(getCachePath(filePath, false), "utf8");
    return JSON.parse(raw) as CachedResult;
  } catch {
    return null;
  }
}
