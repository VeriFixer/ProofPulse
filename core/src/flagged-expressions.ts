/**
 * Pick the expressions to report as not fully covered.
 *
 * Coverage is computed per expression span, and spans nest (a clause
 * `0 <= i <= n` contains `0 <= i` and `i <= n`). Reporting every flagged span,
 * or whole lines, points at the wrong deletion. The rule:
 *
 * - a flagged span whose sub-spans all share its status is reported whole,
 *   and its sub-spans are not reported again;
 * - otherwise only its innermost flagged sub-spans are reported (the span
 *   itself only if it has none).
 *
 * Implicit checks the verifier adds (null, range, termination, ...) are hidden
 * unless `includeImplicit` is set, or they are vacuous: a vacuous proof is a
 * defect wherever it shows up.
 */
import { NodeKind } from "./report/coverage-report.js";
import { CovStatus, type SourceLocation } from "./types.js";
import type { ProofNode } from "./proof-node.js";

export interface FlaggedExpressionOptions {
  includeImplicit?: boolean;
}

export function isImplicitCheck(node: ProofNode): boolean {
  return node.kinds.length > 0 && node.kinds.every(k => k === NodeKind.ImplicitCheck);
}

function before(a: SourceLocation, b: SourceLocation): number {
  return a.line !== b.line ? a.line - b.line : a.col - b.col;
}

/** `outer` strictly contains `inner` (same span counts as not contained). */
function strictlyContains(outer: ProofNode, inner: ProofNode): boolean {
  const s = before(outer.start, inner.start);
  const e = before(inner.end, outer.end);
  return s <= 0 && e <= 0 && (s !== 0 || e !== 0);
}

/** Status ordering, worst first; used to merge nodes that share a span. */
const SEVERITY: Record<CovStatus, number> = {
  [CovStatus.Vacuous]: 0,
  [CovStatus.Uncovered]: 1,
  [CovStatus.CovTest]: 2,
  [CovStatus.CovComplete]: 3,
};

/** Flagged (non-CovComplete) expressions to report, sorted by position. */
export function flaggedExpressions(nodes: ProofNode[], options?: FlaggedExpressionOptions): ProofNode[] {
  const includeImplicit = options?.includeImplicit ?? false;
  const visible = nodes.filter(n =>
    includeImplicit || !isImplicitCheck(n) || n.getCovStatus() === CovStatus.Vacuous);

  // Several nodes can share one span (e.g. a code node and a check on it);
  // keep the worst one per span so each expression is reported once.
  const bySpan = new Map<string, ProofNode>();
  for (const n of visible) {
    const key = `${n.file}|${n.start.line},${n.start.col}-${n.end.line},${n.end.col}`;
    const prev = bySpan.get(key);
    if (!prev || SEVERITY[n.getCovStatus()] < SEVERITY[prev.getCovStatus()]) bySpan.set(key, n);
  }
  const spans = [...bySpan.values()];
  const flagged = spans.filter(n => n.getCovStatus() !== CovStatus.CovComplete);

  // Outermost first, so a whole-clause report hides its sub-spans.
  const order = [...flagged].sort((a, b) => before(a.start, b.start) || before(b.end, a.end));
  const shown: ProofNode[] = [];
  const wholeShown: ProofNode[] = [];

  for (const node of order) {
    if (wholeShown.some(w => w.file === node.file && strictlyContains(w, node))) continue;

    const inside = spans.filter(o => o !== node && o.file === node.file && strictlyContains(node, o));
    const status = node.getCovStatus();
    if (inside.every(o => o.getCovStatus() === status)) {
      shown.push(node);
      wholeShown.push(node);
    } else if (!inside.some(o => o.getCovStatus() !== CovStatus.CovComplete)) {
      shown.push(node);
    }
  }

  return shown.sort((a, b) => before(a.start, b.start) || before(a.end, b.end));
}

const TOKEN_CHAR = /[A-Za-z0-9_'?]/;

/**
 * Inclusive 1-based end column of a span whose reported end column is the
 * start of its last token (as Dafny reports it): extends over the rest of
 * that token, so `n < arr.Length` is not cut to `n < arr.L`.
 */
export function spanEndCol(lineText: string, endCol: number): number {
  let end = endCol;
  if (!TOKEN_CHAR.test(lineText[end - 1] ?? "")) return end;
  while (end < lineText.length && TOKEN_CHAR.test(lineText[end])) end++;
  // A real literal such as `0.0` is one token
  if (/^\d+$/.test(tokenBefore(lineText, end)) && lineText[end] === "." && /\d/.test(lineText[end + 1] ?? "")) {
    end++;
    while (end < lineText.length && /\d/.test(lineText[end])) end++;
  }
  return end;
}

/** The run of token characters ending just before 0-based index `end`. */
function tokenBefore(lineText: string, end: number): string {
  let start = end;
  while (start > 0 && TOKEN_CHAR.test(lineText[start - 1])) start--;
  return lineText.slice(start, end);
}
