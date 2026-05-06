/**
 * Interactive z3 wrapper — drop-in z3 replacement for Boogie.
 * Port of Python z3-minimizer-wrapper.py.
 *
 * Proxies stdin/stdout to real z3, intercepts check-sat + get-unsat-core
 * sequences to perform unsat-core minimization.
 */

import { spawn, execSync, type ChildProcess } from "node:child_process";
import { appendFileSync } from "node:fs";
import { createStdinReader } from "./stdin-reader.js";
import {
  type Command,
  firstHead,
  extractNamedLabel,
  parsePositiveIntCommand,
} from "./smt2-parser.js";
import { minimizeCoreForBlock } from "./minimizer.js";

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const SENTINEL = "__PP_SENTINEL__";

const QUERY_COMMANDS = new Set([
  "check-sat",
  "check-sat-assuming",
  "get-unsat-core",
  "get-model",
  "get-assignment",
  "get-value",
  "get-proof",
  "get-info",
  "echo",
]);

// ---------------------------------------------------------------------------
// Config from environment
// ---------------------------------------------------------------------------

const Z3_PATH = process.env["PROOFPULSE_Z3_PATH"] || "z3";
const LOG_FILE = process.env["PROOFPULSE_WRAPPER_LOG"] || "";

function log(msg: string): void {
  if (LOG_FILE) {
    appendFileSync(LOG_FILE, msg + "\n");
  }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeCmd(text: string): Command {
  const head = firstHead(text);
  const label = head === "assert" ? extractNamedLabel(text) : null;
  return { text, head, label };
}

type SolverState = Command[][];

/**
 * Persistent line reader for z3's stdout.
 * Buffers data continuously so no data is lost between sentinel reads.
 */
function createZ3Reader(z3Stdout: NodeJS.ReadableStream) {
  const pendingLines: string[] = [];
  let partial = "";
  let closed = false;
  let waitResolve: (() => void) | null = null;

  z3Stdout.on("data", (chunk: Buffer) => {
    partial += chunk.toString("utf-8");
    const parts = partial.split("\n");
    partial = parts.pop()!;
    for (const line of parts) {
      pendingLines.push(line);
    }
    if (waitResolve && pendingLines.length > 0) {
      const r = waitResolve;
      waitResolve = null;
      r();
    }
  });

  z3Stdout.on("close", () => {
    closed = true;
    if (partial) {
      pendingLines.push(partial);
      partial = "";
    }
    if (waitResolve) {
      const r = waitResolve;
      waitResolve = null;
      r();
    }
  });

  z3Stdout.on("error", () => {
    closed = true;
    if (waitResolve) {
      const r = waitResolve;
      waitResolve = null;
      r();
    }
  });

  async function readUntilSentinel(): Promise<string> {
    const lines: string[] = [];
    while (true) {
      // Wait for data if none available
      while (pendingLines.length === 0 && !closed) {
        await new Promise<void>((resolve) => {
          waitResolve = resolve;
        });
      }

      if (pendingLines.length === 0 && closed) {
        // z3 exited — return what we have
        return lines.join("\n");
      }

      const line = pendingLines.shift()!;
      if (line.includes(SENTINEL)) {
        return lines.join("\n");
      }
      lines.push(line);
    }
  }

  return { readUntilSentinel };
}

/**
 * Flatten frames into a single command list (current context).
 */
function currentContext(frames: SolverState): Command[] {
  const out: Command[] = [];
  for (const frame of frames) {
    for (const cmd of frame) {
      out.push(cmd);
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

export async function main(): Promise<number> {
  // Handle -version: Boogie calls this first
  if (process.argv.includes("-version")) {
    try {
      const out = execSync(`${Z3_PATH} -version`, { encoding: "utf-8" });
      process.stdout.write(out);
      return 0;
    } catch (e: unknown) {
      const err = e as { status?: number; stdout?: string; stderr?: string };
      if (err.stdout) process.stdout.write(err.stdout);
      if (err.stderr) process.stderr.write(err.stderr);
      return err.status ?? 1;
    }
  }

  log(`wrapper started, z3=${Z3_PATH}, args=${JSON.stringify(process.argv.slice(2))}`);

  // Start real z3 for the live proxy session
  const extraArgs = process.argv.slice(2).filter((a) => a !== "-smt2" && a !== "-in");
  const z3Args = [...extraArgs, "-smt2", "-in"];
  const z3Proc = spawn(Z3_PATH, z3Args, {
    stdio: ["pipe", "pipe", "pipe"],
  });

  // Track solver state for minimization
  const frames: SolverState = [[]];
  let timeoutMs: number | undefined;

  // Track last check-sat for get-unsat-core pairing
  let lastCheckSatCmd: Command = { text: "(check-sat)", head: "check-sat", label: null };

  const reader = createStdinReader(process.stdin);
  const z3Reader = createZ3Reader(z3Proc.stdout!);

  function emit(text: string): void {
    process.stdout.write(text + "\n");
  }

  /** Send command to z3 + sentinel, read until sentinel */
  async function forwardToZ3(cmdText: string): Promise<string> {
    z3Proc.stdin!.write(cmdText + "\n");
    z3Proc.stdin!.write(`(echo "${SENTINEL}")\n`);
    return z3Reader.readUntilSentinel();
  }

  try {
    while (true) {
      const raw = await reader.readCommand();
      if (!raw) break;

      const cmd = makeCmd(raw);
      const head = cmd.head;
      log(`cmd: ${head} | ${raw.slice(0, 80)}`);

      // --- Detect (set-option :timeout N) ---
      if (head === "set-option") {
        const m = raw.match(/:timeout\s+(\d+)/);
        if (m) {
          timeoutMs = parseInt(m[1], 10);
          log(`timeout set to ${timeoutMs}ms`);
        }
      }

      // --- State tracking ---
      if (head === "push") {
        const count = parsePositiveIntCommand(cmd.text, "push");
        for (let i = 0; i < count; i++) {
          frames.push([]);
        }
        const resp = await forwardToZ3(raw);
        if (resp) emit(resp);
        continue;
      }

      if (head === "pop") {
        const count = parsePositiveIntCommand(cmd.text, "pop");
        for (let i = 0; i < count; i++) {
          if (frames.length > 1) {
            frames.pop();
          }
        }
        const resp = await forwardToZ3(raw);
        if (resp) emit(resp);
        continue;
      }

      if (head === "reset") {
        frames.length = 0;
        frames.push([]);
        const resp = await forwardToZ3(raw);
        if (resp) emit(resp);
        continue;
      }

      // --- Query block: check-sat possibly followed by get-unsat-core ---
      if (head === "check-sat" || head === "check-sat-assuming") {
        const statusResp = await forwardToZ3(raw);
        log(`check-sat response: ${statusResp}`);
        emit(statusResp);
        lastCheckSatCmd = cmd;
        continue;
      }

      if (head === "get-unsat-core") {
        // Get the core from live z3
        const coreResp = await forwardToZ3(raw);
        log(`get-unsat-core response: ${coreResp.slice(0, 200)}`);

        // Try to minimize
        try {
          const ctx = currentContext(frames);
          const queryBlock: Command[] = [lastCheckSatCmd, cmd];

          // Parse the core from z3's response
          const coreText = coreResp.trim();
          let initialCore: string[] = [];
          if (coreText.startsWith("(")) {
            const inner = coreText.slice(1, -1).trim();
            initialCore = inner ? inner.split(/\s+/) : [];
          }

          if (initialCore.length > 0) {
            // Do NOT pass Boogie's per-query timeout to minimization.
            // Minimization spawns fresh z3 on full context — needs more time.
            // Passing the tight Boogie timeout causes all trials to time out,
            // making every label appear "required" (no minimization).
            const minimized = await minimizeCoreForBlock(
              Z3_PATH,
              ctx,
              queryBlock,
              initialCore,
              undefined
            );
            emit("(" + minimized.join(" ") + ")");
            log(`minimized core: ${initialCore.length} -> ${minimized.length}`);
          } else {
            emit(coreResp);
          }
        } catch (e: unknown) {
          log(`minimization failed, passing through: ${e}`);
          emit(coreResp);
        }
        continue;
      }

      // --- Other query commands: forward transparently ---
      if (head !== null && QUERY_COMMANDS.has(head)) {
        const resp = await forwardToZ3(raw);
        emit(resp);
        continue;
      }

      // --- Non-query command (assert, declare, define, set-option, etc.) ---
      if (cmd.label !== null || head === "assert") {
        frames[frames.length - 1].push(cmd);
      } else if (
        head === "declare-fun" ||
        head === "declare-sort" ||
        head === "declare-const" ||
        head === "declare-datatypes" ||
        head === "define-fun" ||
        head === "define-sort" ||
        head === "set-option" ||
        head === "set-info" ||
        head === "set-logic"
      ) {
        frames[frames.length - 1].push(cmd);
      }

      const resp = await forwardToZ3(raw);
      if (resp) emit(resp);
    }
  } catch (e: unknown) {
    log(`wrapper error: ${e}`);
  } finally {
    try {
      z3Proc.stdin!.end();
    } catch {
      // ignore
    }
    await new Promise<void>((resolve) => {
      z3Proc.on("close", () => resolve());
      // If already exited
      if (z3Proc.exitCode !== null) resolve();
    });
    log("wrapper done");
  }

  return 0;
}

// CLI entry point
const isMain =
  process.argv[1] &&
  (process.argv[1].endsWith("wrapper.js") || process.argv[1].endsWith("wrapper.ts"));

if (isMain) {
  main().then((code) => process.exit(code));
}
