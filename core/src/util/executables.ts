import { accessSync, constants as fsConstants, existsSync } from "node:fs";
import { delimiter, join } from "node:path";
import { platform } from "node:os";
import { execFileSync } from "node:child_process";

export const IS_WIN = platform() === "win32";
export const IS_MAC = platform() === "darwin";

export function isExecutableFile(filePath: string): boolean {
  if (!existsSync(filePath)) return false;
  if (IS_WIN) return true;
  try {
    accessSync(filePath, fsConstants.X_OK);
    return true;
  } catch {
    return false;
  }
}

export function resolveExecutableInPath(executableName: string): string | undefined {
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
export function probeVersion(bin: string, arg: string): string | undefined {
  try {
    const out = execFileSync(bin, [arg], { encoding: "utf-8", timeout: 5000, stdio: ["ignore", "pipe", "pipe"] });
    return out.trim().split("\n")[0];
  } catch {
    return undefined;
  }
}
