/**
 * Batch CLI entry point — port of Python minimize_unsat_core_trace.py main() + process_file().
 *
 * Usage: node batch.js <smt2-file> --z3 PATH --output PATH --quiet
 * Exit codes: 0 success, 1 parse error, 2 z3 not found
 */

import { readFile, writeFile } from "node:fs/promises";
import { accessSync, constants } from "node:fs";
import {
  type Command,
  SMT2Error,
  splitTopLevel,
  firstHead,
  extractNamedLabel,
  parsePositiveIntCommand,
} from "./smt2-parser.js";
import { buildScript, minimizeCoreForBlock } from "./minimizer.js";
import { runZ3, parseStatus, parseCoreFromMarkedOutput } from "./z3-runner.js";

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

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
// Types
// ---------------------------------------------------------------------------

type SolverState = Command[][];

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function parseArgs(argv: string[]): {
  smt2: string;
  z3: string;
  output: string | null;
  quiet: boolean;
} {
  const args = argv.slice(2); // skip node + script
  let smt2 = "";
  let z3 = "z3";
  let output: string | null = null;
  let quiet = false;

  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === "--z3") {
      z3 = args[++i] ?? "z3";
    } else if (a === "--output") {
      output = args[++i] ?? null;
    } else if (a === "--quiet") {
      quiet = true;
    } else if (!a.startsWith("-")) {
      smt2 = a;
    }
  }

  return { smt2, z3, output, quiet };
}

function currentContext(frames: SolverState): Command[] {
  const out: Command[] = [];
  for (const frame of frames) {
    for (const cmd of frame) {
      out.push(cmd);
    }
  }
  return out;
}

function parseCommandsFromText(text: string): Command[] {
  const raw = splitTopLevel(text);
  return raw.map((expr) => {
    const head = firstHead(expr);
    const label = extractNamedLabel(expr);
    return { text: expr, head, label };
  });
}

// ---------------------------------------------------------------------------
// process_file port
// ---------------------------------------------------------------------------

async function processFile(
  z3Bin: string,
  commands: Command[],
  quiet: boolean
): Promise<string> {
  const frames: SolverState = [[]];
  const outChunks: string[] = [];
  let i = 0;
  let blockIndex = 0;

  while (i < commands.length) {
    const cmd = commands[i];
    const head = cmd.head;

    if (head === "push") {
      const count = parsePositiveIntCommand(cmd.text, "push");
      for (let k = 0; k < count; k++) {
        frames.push([]);
      }
      i++;
      continue;
    }

    if (head === "pop") {
      const count = parsePositiveIntCommand(cmd.text, "pop");
      if (count >= frames.length) {
        throw new SMT2Error(`Pop underflow: ${cmd.text}`);
      }
      for (let k = 0; k < count; k++) {
        frames.pop();
      }
      i++;
      continue;
    }

    if (head === "reset") {
      frames.length = 0;
      frames.push([]);
      i++;
      continue;
    }

    if (head === "check-sat" || head === "check-sat-assuming") {
      blockIndex++;
      const queryBlock: Command[] = [cmd];
      i++;
      while (
        i < commands.length &&
        commands[i].head !== null &&
        QUERY_COMMANDS.has(commands[i].head!) &&
        commands[i].head !== "check-sat" &&
        commands[i].head !== "check-sat-assuming"
      ) {
        queryBlock.push(commands[i]);
        i++;
      }

      const contextCmds = currentContext(frames);
      const originalScript = buildScript(contextCmds, null, queryBlock, true);
      const proc = await runZ3(z3Bin, originalScript);

      if (proc.exitCode >= 2) {
        throw new SMT2Error(
          `Z3 failed on query block ${blockIndex}.\nstdout:\n${proc.stdout}\n\nstderr:\n${proc.stderr}`
        );
      }

      const status = parseStatus(proc.stdout);
      const requestedCore = queryBlock.some((q) => q.head === "get-unsat-core");

      if (!requestedCore || status !== "unsat") {
        // Forward z3 output without marker
        const rendered = await runZ3(
          z3Bin,
          buildScript(contextCmds, null, queryBlock, false)
        );
        if (rendered.exitCode >= 2) {
          throw new SMT2Error(
            `Z3 failed rendering block ${blockIndex}.\nstdout:\n${rendered.stdout}\n\nstderr:\n${rendered.stderr}`
          );
        }
        outChunks.push(rendered.stdout);
        if (rendered.stderr && !quiet) {
          outChunks.push(rendered.stderr);
        }
        continue;
      }

      // Minimize
      const initialCore = parseCoreFromMarkedOutput(proc.stdout);
      const minimizedCore = await minimizeCoreForBlock(
        z3Bin,
        contextCmds,
        queryBlock,
        initialCore
      );

      if (!quiet) {
        process.stderr.write(
          `; [block ${blockIndex}] initial core size ${initialCore.length} -> minimized size ${minimizedCore.length}\n`
        );
      }

      const finalScript = buildScript(
        contextCmds,
        new Set(minimizedCore),
        queryBlock,
        false
      );
      const finalProc = await runZ3(z3Bin, finalScript);
      if (finalProc.exitCode >= 2) {
        throw new SMT2Error(
          `Z3 failed rendering minimized block ${blockIndex}.\nstdout:\n${finalProc.stdout}\n\nstderr:\n${finalProc.stderr}`
        );
      }
      outChunks.push(finalProc.stdout);
      if (finalProc.stderr && !quiet) {
        outChunks.push(finalProc.stderr);
      }
      continue;
    }

    // Non-query command: accumulate in current frame
    frames[frames.length - 1].push(cmd);
    i++;
  }

  return outChunks.join("");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

export async function main(): Promise<number> {
  const { smt2, z3, output, quiet } = parseArgs(process.argv);

  if (!smt2) {
    process.stderr.write("error: no input SMT2 file specified\n");
    return 1;
  }

  try {
    const text = await readFile(smt2, "utf-8");
    const commands = parseCommandsFromText(text);
    const result = await processFile(z3, commands, quiet);

    if (output !== null) {
      await writeFile(output, result, "utf-8");
    } else {
      process.stdout.write(result);
    }
    return 0;
  } catch (e: unknown) {
    if (
      e instanceof Error &&
      "code" in e &&
      (e as NodeJS.ErrnoException).code === "ENOENT"
    ) {
      // Could be file not found or z3 not found
      // Check if it's the z3 binary
      try {
        accessSync(smt2, constants.R_OK);
        // smt2 file exists, so z3 binary not found
        process.stderr.write(`error: could not find z3 binary: ${z3}\n`);
        return 2;
      } catch {
        // smt2 file not found — also treat as z3-not-found if z3 spawn failed,
        // but if the smt2 file itself is missing, it's a file error
        process.stderr.write(
          `error: could not find z3 binary: ${z3}\n`
        );
        return 2;
      }
    }
    if (e instanceof SMT2Error) {
      process.stderr.write(`error: ${e.message}\n`);
      return 1;
    }
    // Unknown error — treat as parse error
    process.stderr.write(
      `error: ${e instanceof Error ? e.message : String(e)}\n`
    );
    return 1;
  }
}

// CLI entry point
const isMain =
  process.argv[1] &&
  (process.argv[1].endsWith("batch.js") || process.argv[1].endsWith("batch.ts"));

if (isMain) {
  main().then((code) => process.exit(code));
}
