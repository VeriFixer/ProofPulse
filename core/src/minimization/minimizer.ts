/**
 * Core minimization algorithm — ported from Python minimize_unsat_core_trace.py
 */

import { readFile, stat, unlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { randomBytes } from "node:crypto";
import { Command, SMT2Error, SmtCommand } from "./smt2-parser.js";
import { parseTriggerTrace, triggerSuppliers } from "./trigger-trace.js";
import { runZ3, parseStatus, parseCoreFromMarkedOutput, SolverStatus } from "./z3-runner.js";

const CORE_MARKER = "__UNSAT_CORE_MARKER__";

const SWITCH_RE = /^\(\s*assert\s+\(\s*!\s+([^\s()]+)\s+:named\s+[^\s()]+\s*\)\s*\)$/s;

/**
 * A dropped fact's switch, turned off. A tracked fact is `(=> g F)` with the
 * switch `(assert (! g :named ...))`; leaving `g` free is not enough, since z3
 * may still try `g` and keep the quantifier instances F's terms triggered
 * (instances stay valid after backtracking). Asserting `(not g)` keeps F
 * irrelevant, so its terms trigger nothing, as when the fact is deleted.
 */
function switchOff(text: string): string | null {
  const m = text.trim().match(SWITCH_RE);
  return m ? `(assert (not ${m[1]}))` : null;
}

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
      const off = switchOff(cmd.text);
      if (off) parts.push(off);
      continue;
    }
    parts.push(cmd.text);
  }

  if (addMarker) {
    for (const q of queryBlock) {
      if (q.head === SmtCommand.GetUnsatCore) {
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
 * Whether the facts with these labels prove the goal on their own: the query
 * re-run with every other labelled fact dropped is unsat. A timeout or an
 * unknown counts as not proved.
 */
export async function provesAlone(
  z3Bin: string,
  contextCmds: Command[],
  queryBlock: Command[],
  labels: string[],
  timeoutMs?: number
): Promise<boolean> {
  const result = await runZ3(z3Bin, buildScript(contextCmds, new Set(labels), queryBlock, false), timeoutMs);
  if (result.timedOut) return false;
  if (result.exitCode >= 2) {
    throw new SMT2Error(`Z3 failed while checking a core.\nstdout:\n${result.stdout}\n\nstderr:\n${result.stderr}`);
  }
  return parseStatus(result.stdout) === SolverStatus.Unsat;
}

/** How `sufficientCore` got its answer. */
export enum CoreCheck {
  /** z3's core proves the goal on its own. */
  Core = "core",
  /** The core plus facts that supplied trigger terms, read from z3's trace. */
  Trace = "trace",
  /** Neither did: every active fact is kept (the original query). */
  AllFacts = "all-facts",
}

/** Traces larger than this are not read; the query keeps all its facts. */
const MAX_TRACE_BYTES = 200 * 1024 * 1024;

/**
 * Labels of facts that supplied trigger terms to the instantiations `core`
 * relies on, from a trace of the original query (all facts kept).
 */
async function traceSuppliers(
  z3Bin: string,
  contextCmds: Command[],
  queryBlock: Command[],
  core: string[],
  timeoutMs?: number
): Promise<string[]> {
  const tracePath = join(tmpdir(), `proofpulse-trace-${randomBytes(8).toString("hex")}.log`);
  try {
    const result = await runZ3(z3Bin, buildScript(contextCmds, null, queryBlock, false), timeoutMs,
      ["trace=true", `trace_file_name=${tracePath}`]);
    if (result.timedOut || result.exitCode >= 2) return [];
    if ((await stat(tracePath)).size > MAX_TRACE_BYTES) return [];
    return triggerSuppliers(parseTriggerTrace(await readFile(tracePath, "utf-8")), new Set(core));
  } catch {
    return [];
  } finally {
    await unlink(tracePath).catch(() => {});
  }
}

/**
 * A core that proves the goal on its own. Z3's unsat core leaves out facts
 * whose only part in the proof was to supply a term that triggered a
 * quantifier, so the core is checked alone first. When it does not prove the
 * goal, the facts that supplied trigger terms are read from z3's trace and
 * added (those the core proves without are dropped again); when that does not
 * prove the goal either, every active fact is kept (the original query).
 */
export async function sufficientCore(
  z3Bin: string,
  contextCmds: Command[],
  queryBlock: Command[],
  core: string[],
  timeoutMs?: number
): Promise<{ core: string[]; check: CoreCheck }> {
  const activeLabels = activeLabelsInContext(contextCmds);
  const normalized = normalizeCore(core, activeLabels);
  const proves = (labels: string[]) => provesAlone(z3Bin, contextCmds, queryBlock, labels, timeoutMs);
  if (await proves(normalized)) {
    return { core: normalized, check: CoreCheck.Core };
  }

  const suppliers = await traceSuppliers(z3Bin, contextCmds, queryBlock, normalized, timeoutMs);
  if (suppliers.length > 0 && await proves([...normalized, ...suppliers])) {
    // The trace walk over-approximates (it follows every instantiation of the
    // kept quantifiers): drop suppliers the goal is proved without.
    const needed = [...suppliers];
    for (const s of suppliers) {
      const without = needed.filter((n) => n !== s);
      if (await proves([...normalized, ...without])) needed.splice(needed.indexOf(s), 1);
    }
    return { core: [...normalized, ...needed], check: CoreCheck.Trace };
  }
  return { core: [...activeLabels], check: CoreCheck.AllFacts };
}

/**
 * Iteratively minimize unsat core by removing labels one at a time.
 *
 * - Remove label → run z3 → if still unsat, use new smaller core and restart
 *   (only when that core proves the goal on its own, else just drop the label)
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
    if (status === SolverStatus.Unsat) {
      const newCore = normalizeCore(parseCoreFromMarkedOutput(result.stdout), trialKept);
      // Z3's core can leave out facts that supplied trigger terms; the trial itself proved the goal
      const smaller = newCore.length < trial.length;
      active = smaller && !(await provesAlone(z3Bin, contextCmds, queryBlock, newCore, timeoutMs)) ? trial : newCore;
      i = 0;
    } else {
      i++;
    }
  }

  return active;
}
