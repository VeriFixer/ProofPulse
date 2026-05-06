/**
 * Z3 subprocess runner — ported from Python minimize_unsat_core_trace.py run_z3()
 */

import { spawn } from "node:child_process";
import { writeFile, unlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { randomBytes } from "node:crypto";
import { SMT2Error, extractFirstBalancedSexpr, parseCoreExpr } from "./smt2-parser.js";

export interface Z3Result {
  stdout: string;
  stderr: string;
  exitCode: number;
  timedOut: boolean;
}

const CORE_MARKER = "__UNSAT_CORE_MARKER__";
const STATUS_RE = /(?:^|\n)(sat|unsat|unknown)\s*$/m;

/**
 * Run z3 on a script string via temp file. Optional timeout in ms.
 * No default timeout — only applies when caller provides one.
 * Temp file deleted in finally block.
 */
export async function runZ3(
  z3Bin: string,
  scriptText: string,
  timeoutMs?: number
): Promise<Z3Result> {
  const tmpPath = join(
    tmpdir(),
    `proofpulse-${randomBytes(8).toString("hex")}.smt2`
  );
  await writeFile(tmpPath, scriptText, "utf-8");

  try {
    return await new Promise<Z3Result>((resolve) => {
      const child = spawn(z3Bin, ["-smt2", tmpPath], {
        stdio: ["ignore", "pipe", "pipe"],
      });

      const stdoutChunks: Buffer[] = [];
      const stderrChunks: Buffer[] = [];
      let timedOut = false;
      let timer: ReturnType<typeof setTimeout> | undefined;

      child.stdout.on("data", (chunk: Buffer) => stdoutChunks.push(chunk));
      child.stderr.on("data", (chunk: Buffer) => stderrChunks.push(chunk));

      if (timeoutMs !== undefined) {
        timer = setTimeout(() => {
          timedOut = true;
          child.kill("SIGKILL");
        }, timeoutMs);
      }

      child.on("close", (code) => {
        if (timer !== undefined) clearTimeout(timer);
        resolve({
          stdout: Buffer.concat(stdoutChunks).toString("utf-8"),
          stderr: Buffer.concat(stderrChunks).toString("utf-8"),
          exitCode: code ?? 1,
          timedOut,
        });
      });
    });
  } finally {
    try {
      await unlink(tmpPath);
    } catch {
      // ignore cleanup errors
    }
  }
}

/**
 * Parse solver status (sat/unsat/unknown) from z3 stdout.
 * Throws SMT2Error if not found.
 */
export function parseStatus(stdout: string): string {
  const m = STATUS_RE.exec(stdout);
  if (!m) {
    throw new SMT2Error(`Could not find solver status in output:\n${stdout}`);
  }
  return m[1];
}

/**
 * Parse unsat core from marked output (after CORE_MARKER echo).
 * Throws SMT2Error if marker or core not found.
 */
export function parseCoreFromMarkedOutput(stdout: string): string[] {
  const markerPos = stdout.indexOf(CORE_MARKER);
  if (markerPos === -1) {
    throw new SMT2Error(
      `Did not find unsat-core marker in output:\n${stdout}`
    );
  }
  const tail = stdout.slice(markerPos + CORE_MARKER.length);
  const expr = extractFirstBalancedSexpr(tail);
  if (expr === null) {
    throw new SMT2Error(
      `Could not parse unsat core after marker:\n${stdout}`
    );
  }
  return parseCoreExpr(expr);
}
