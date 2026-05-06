/**
 * Core minimization algorithm — ported from Python minimize_unsat_core_trace.py
 */

import { Command, SMT2Error } from "./smt2-parser.js";
import { runZ3, parseStatus, parseCoreFromMarkedOutput } from "./z3-runner.js";

const CORE_MARKER = "__UNSAT_CORE_MARKER__";

/**
 * Build SMT2 script from context commands, filtering by kept labels.
 * If keptLabels is null, all commands are included.
 * If addMarker is true, inserts an echo marker before get-unsat-core.
 */
export function buildScript(
  commands: Command[],
  keptLabels: Set<string> | null,
  queryBlock: Command[],
  addMarker: boolean
): string {
  const parts: string[] = [];

  for (const cmd of commands) {
    if (cmd.label !== null && keptLabels !== null && !keptLabels.has(cmd.label)) {
      continue;
    }
    parts.push(cmd.text);
  }

  if (addMarker) {
    for (const q of queryBlock) {
      if (q.head === "get-unsat-core") {
        parts.push(`(echo "${CORE_MARKER}")`);
      }
      parts.push(q.text);
    }
  } else {
    for (const q of queryBlock) {
      parts.push(q.text);
    }
  }

  return parts.join("\n") + "\n";
}

/**
 * Get all active labels in current context. Throws on duplicates.
 */
export function activeLabelsInContext(commands: Command[]): Set<string> {
  const seen = new Set<string>();
  const dups: string[] = [];

  for (const cmd of commands) {
    if (cmd.label !== null) {
      if (seen.has(cmd.label)) {
        dups.push(cmd.label);
      }
      seen.add(cmd.label);
    }
  }

  if (dups.length > 0) {
    const unique = [...new Set(dups)].sort();
    throw new SMT2Error(
      `Duplicate active labels in same solver state: ${unique.join(", ")}`
    );
  }

  return seen;
}

/**
 * Normalize core: deduplicate, validate against active labels.
 * Throws if a label is not in activeLabels.
 */
export function normalizeCore(core: string[], activeLabels: Set<string>): string[] {
  const seen = new Set<string>();
  const out: string[] = [];

  for (const lbl of core) {
    if (!activeLabels.has(lbl)) {
      throw new SMT2Error(
        `Z3 returned label not active in current context: ${lbl}`
      );
    }
    if (!seen.has(lbl)) {
      seen.add(lbl);
      out.push(lbl);
    }
  }

  return out;
}

/**
 * Iteratively minimize unsat core by removing labels one at a time.
 *
 * - Remove label → run z3 → if still unsat, use new smaller core and restart
 * - If sat/unknown, keep label and advance
 * - On z3 timeout (if timeoutMs provided): treat label as required, continue
 * - On z3 exit code ≥ 2: throw SMT2Error
 */
export async function minimizeCoreForBlock(
  z3Bin: string,
  contextCmds: Command[],
  queryBlock: Command[],
  initialCore: string[],
  timeoutMs?: number
): Promise<string[]> {
  const activeLabels = activeLabelsInContext(contextCmds);
  let active = normalizeCore(initialCore, activeLabels);

  let i = 0;
  while (i < active.length) {
    const trial = [...active.slice(0, i), ...active.slice(i + 1)];
    const trialKept = new Set(trial);
    const script = buildScript(contextCmds, trialKept, queryBlock, true);
    const result = await runZ3(z3Bin, script, timeoutMs);

    if (result.timedOut) {
      // Timeout: treat label as required, continue
      i++;
      continue;
    }

    if (result.exitCode >= 2) {
      throw new SMT2Error(
        `Z3 failed during minimization.\nstdout:\n${result.stdout}\n\nstderr:\n${result.stderr}`
      );
    }

    const status = parseStatus(result.stdout);
    if (status === "unsat") {
      const newCore = parseCoreFromMarkedOutput(result.stdout);
      active = normalizeCore(newCore, trialKept);
      i = 0;
    } else {
      i++;
    }
  }

  return active;
}
