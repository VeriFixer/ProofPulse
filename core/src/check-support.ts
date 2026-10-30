/**
 * Coverage of what checks rely on.
 *
 * A check is a goal the verifier adds itself (index in range, function
 * precondition, termination, ...) rather than a clause the user wrote. What a
 * check uses is needed only so that the expression holding the check makes
 * sense, so it is treated like what proves that expression:
 *
 * - what makes a postcondition well-defined is covered, like what proves it,
 *   even when no caller uses the postcondition (a lemma's `requires n < |s|`
 *   for its `ensures ... s[n]`);
 * - an invariant that only makes another uncovered invariant well-defined stays
 *   uncovered: the two can be removed together.
 *
 * A check that sits in code rather than in a clause makes what it uses
 * covered: the code is the program, and it is not up for removal.
 *
 * A call's precondition, proved at the call site, is the same kind of check
 * with the call as its holder: what it uses has (at best) the call's status.
 * A lemma call that only serves unused assertions takes its preconditions'
 * support down with it.
 *
 * Checks are read from every unit of the report, whatever its kind, so this
 * does not depend on how a verifier splits its proofs (Dafny reports
 * well-formedness in units of their own).
 */
import { CovStatus, TokenType, type SourceLocation } from "./types.js";
import type { ProofNode } from "./proof-node.js";
import type { ProofGraph } from "./proof-graph.js";
import { type CoverageReport, NodeKind, type ReportNode, type ReportSpan } from "./report/coverage-report.js";

/** A span with the source path resolved. */
export interface PathSpan {
  file: string;
  start: SourceLocation;
  end: SourceLocation;
}

/**
 * One check: the clauses that hold it, innermost first (none when it sits in
 * code), and the nodes its proof used.
 */
export interface CheckSupport {
  containers: PathSpan[];
  /** The goal is a callee precondition at a call site; `containers` is the call. */
  call?: boolean;
  used: Array<{ span: PathSpan; clause: boolean }>;
}

/** Kinds the user writes as clauses; their parts can be removed, unlike code. */
const CLAUSE_KINDS: ReadonlySet<NodeKind> = new Set([
  NodeKind.Precondition,
  NodeKind.Postcondition,
  NodeKind.Invariant,
  NodeKind.Assert,
]);

/** Goals that are checks: not written by the user as a clause or fact. */
const CHECK_KINDS: ReadonlySet<NodeKind> = new Set([NodeKind.ImplicitCheck, NodeKind.Code, NodeKind.Other]);

function cmp(a: SourceLocation, b: SourceLocation): number {
  return a.line !== b.line ? a.line - b.line : a.col - b.col;
}

export function spanKey(s: PathSpan): string {
  return `${s.file}|${s.start.line},${s.start.col}-${s.end.line},${s.end.col}`;
}

/** `outer` contains `inner` (equal spans count). */
export function spanContains(outer: PathSpan, inner: PathSpan): boolean {
  return outer.file === inner.file && cmp(outer.start, inner.start) <= 0 && cmp(inner.end, outer.end) <= 0;
}

function spanSize(s: PathSpan): number {
  return (s.end.line - s.start.line) * 10000 + (s.end.col - s.start.col);
}

/** Collect every check of the report with the clause holding it and what it used. */
export function collectCheckSupports(report: CoverageReport): CheckSupport[] {
  const paths = new Map(report.sources.map(s => [s.id, s.path]));
  const nodes = new Map(report.nodes.map(n => [n.id, n]));
  const resolve = (s: ReportSpan): PathSpan => ({ file: paths.get(s.file) ?? s.file, start: s.start, end: s.end });

  const clauses: PathSpan[] = [];
  const seen = new Set<string>();
  for (const n of report.nodes) {
    if (!CLAUSE_KINDS.has(n.kind)) continue;
    const span = resolve(n.span);
    const key = spanKey(span);
    if (!seen.has(key)) { seen.add(key); clauses.push(span); }
  }

  const callSites = new Set<string>();
  for (const n of report.nodes) {
    if (n.kind === NodeKind.CallRequires || n.kind === NodeKind.CallEnsures) callSites.add(spanKey(resolve(n.span)));
  }

  const holdingClauses = (goal: PathSpan): PathSpan[] =>
    clauses.filter(c => spanContains(c, goal)).sort((a, b) => spanSize(a) - spanSize(b));

  const supports: CheckSupport[] = [];
  for (const unit of report.units) {
    for (const query of unit.queries) {
      const goals = query.goals.map(id => nodes.get(id)).filter((n): n is ReportNode => !!n);
      for (const goal of goals) {
        const goalSpan = resolve(goal.span);
        const call = goal.kind === NodeKind.Precondition && callSites.has(spanKey(goalSpan));
        if (!call && !CHECK_KINDS.has(goal.kind)) continue;
        const used = query.used
          .map(id => nodes.get(id))
          .filter((n): n is ReportNode => !!n && n.id !== goal.id)
          .map(n => ({ span: resolve(n.span), clause: CLAUSE_KINDS.has(n.kind) }))
          .filter(u => !spanContains(u.span, goalSpan) && !callSites.has(spanKey(u.span)));
        if (used.length === 0) continue;
        supports.push(call ? { containers: [goalSpan], used, call } : { containers: holdingClauses(goalSpan), used });
      }
    }
  }
  return supports;
}

/** Spans of checks that sit in a clause (their uses inherit that clause's status). */
export function checksInClauses(report: CoverageReport): Set<string> {
  const paths = new Map(report.sources.map(s => [s.id, s.path]));
  const clauses = report.nodes
    .filter(n => CLAUSE_KINDS.has(n.kind))
    .map(n => ({ file: paths.get(n.span.file) ?? n.span.file, start: n.span.start, end: n.span.end }));
  const keys = new Set<string>();
  for (const n of report.nodes) {
    if (!CHECK_KINDS.has(n.kind)) continue;
    const span = { file: paths.get(n.span.file) ?? n.span.file, start: n.span.start, end: n.span.end };
    if (clauses.some(c => spanContains(c, span))) keys.add(spanKey(span));
  }
  return keys;
}

const RANK: Record<CovStatus, number> = {
  [CovStatus.Vacuous]: -1,
  [CovStatus.Uncovered]: 0,
  [CovStatus.CovTest]: 1,
  [CovStatus.CovComplete]: 2,
};

function better(a: CovStatus, b: CovStatus): CovStatus {
  return RANK[a] >= RANK[b] ? a : b;
}

/**
 * Status a holder passes on to what makes it well-defined: the status its
 * provers get. A postcondition's provers are always covered (coverage.ts marks
 * them so whether or not a caller uses it); other holders pass on their own.
 */
function supportStatus(n: ProofNode): CovStatus {
  return n.getType() === TokenType.Postcondition ? better(n.getCovStatus(), n.getCovStatusInternal()) : n.getCovStatus();
}

/**
 * Lift what checks use to the status of the clause holding the check (or to
 * covered for checks in code). A used clause counts its parts as used, since
 * verifiers may report a whole clause where other proofs name its conjuncts.
 * Repeats until nothing changes: a lifted clause can hold further checks.
 */
export function applyCoverageCheckSupport(graph: ProofGraph): void {
  const supports = graph.checkSupports;
  if (supports.length === 0) return;

  const all = graph.getAllNodes();
  const bySpan = new Map<string, ProofNode[]>();
  for (const n of all) {
    const key = spanKey(n);
    const list = bySpan.get(key);
    if (list) list.push(n); else bySpan.set(key, [n]);
  }

  // Status of the innermost holding clause that proofs report on. Verifiers
  // may name sub-clauses only in checks (Dafny: the body of a `forall`), so
  // those are skipped. A check in code, or in clauses no proof reports on,
  // makes what it uses covered.
  const statusOf = (containers: PathSpan[], call: boolean): CovStatus => {
    for (const c of containers) {
      const list = bySpan.get(spanKey(c))?.filter(n => !call || n.getType() === TokenType.Call);
      if (list?.length) return list.reduce<CovStatus>((s, n) => better(s, supportStatus(n)), CovStatus.Uncovered);
    }
    return CovStatus.CovComplete;
  };

  const targetsOf = (u: { span: PathSpan; clause: boolean }): ProofNode[] =>
    u.clause ? all.filter(n => spanContains(u.span, n)) : (bySpan.get(spanKey(u.span)) ?? []);

  // Raise a node and, transitively, what proves it: an invariant that is now
  // needed still needs whatever shows it holds.
  const raise = (node: ProofNode, status: CovStatus): boolean => {
    let changed = false;
    const work: ProofNode[] = [node];
    while (work.length > 0) {
      const n = work.pop()!;
      const next = better(n.getCovStatus(), status);
      if (next === n.getCovStatus() && n !== node) continue;
      if (next !== n.getCovStatus()) { n.setCovStatus(next); changed = true; }
      for (const dep of n.provedBy) if (dep !== n && better(dep.getCovStatus(), status) !== dep.getCovStatus()) work.push(dep);
    }
    return changed;
  };

  let changed = true;
  while (changed) {
    changed = false;
    for (const s of supports) {
      const status = statusOf(s.containers, s.call ?? false);
      if (status === CovStatus.Uncovered) continue;
      for (const u of s.used) {
        for (const t of targetsOf(u)) {
          if (s.containers.some(c => spanContains(t, c))) continue;
          if (raise(t, status)) changed = true;
        }
      }
    }
  }
}
