/**
 * Dafny adapter: Dafny's text verification log → proofpulse-coverage/v1.
 *
 * Uses Dafny's existing `--log-format text` output only; no new Dafny or
 * Boogie reports are needed.
 */
import {
  COVERAGE_REPORT_SCHEMA,
  CoverageReport,
  ReportNode,
  ReportSource,
  ReportTool,
  ReportUnit,
  SolverKind,
  VerifierId,
  isCallKind,
} from "../../report/coverage-report.js";
import type { ParsedBatch } from "./log-parser.js";
import { dafnyMessageKind } from "./messages.js";

/** Callee clause a call-site message points at. */
enum ClauseKind {
  Requires = "requires",
  Ensures = "ensures",
}

interface Located {
  file: string;
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  proofText: string;
}

const CLAUSE_TARGET_RE = /(requires|ensures) clause at\s+(.+?)\((\d+),(\d+)\)\s*-\s*\((\d+),(\d+)\)/;

function parseClauseTarget(message: string): (Omit<Located, "proofText"> & { clause: ClauseKind }) | null {
  const m = message.match(CLAUSE_TARGET_RE);
  if (!m) return null;
  return {
    clause: m[1] === ClauseKind.Requires ? ClauseKind.Requires : ClauseKind.Ensures,
    file: m[2].trim(),
    startLine: parseInt(m[3], 10),
    startCol: parseInt(m[4], 10),
    endLine: parseInt(m[5], 10),
    endCol: parseInt(m[6], 10),
  };
}

export interface DafnyReportInfo {
  version?: string;
  solverVersion?: string;
  minimized?: boolean;
}

class ReportBuilder {
  private readonly sources = new Map<string, ReportSource>();
  private readonly nodes = new Map<string, ReportNode>();
  readonly units: ReportUnit[] = [];

  private sourceId(path: string): string {
    let source = this.sources.get(path);
    if (!source) {
      source = { id: `f${this.sources.size}`, path };
      this.sources.set(path, source);
    }
    return source.id;
  }

  /** Report node for one (location, message) pair; identical pairs share a node. */
  node(loc: Located): string {
    const key = `${loc.file}|${loc.startLine},${loc.startCol}-${loc.endLine},${loc.endCol}|${loc.proofText}`;
    const existing = this.nodes.get(key);
    if (existing) return existing.id;

    const kind = dafnyMessageKind(loc.proofText);
    const node: ReportNode = {
      id: `n${this.nodes.size}`,
      kind,
      span: {
        file: this.sourceId(loc.file),
        start: { line: loc.startLine, col: loc.startCol },
        end: { line: loc.endLine, col: loc.endCol },
      },
      message: loc.proofText,
    };
    this.nodes.set(key, node);

    if (isCallKind(kind)) {
      const target = parseClauseTarget(loc.proofText);
      if (target) {
        node.callTargets = [this.node({ ...target, proofText: `${target.clause} clause` })];
      }
    }
    return node.id;
  }

  build(info: DafnyReportInfo): CoverageReport {
    const tool: ReportTool = { name: VerifierId.Dafny };
    if (info.version) tool.version = info.version;
    tool.solver = { kind: SolverKind.Z3, ...(info.solverVersion ? { version: info.solverVersion } : {}) };
    if (info.minimized !== undefined) tool.minimized = info.minimized;
    return {
      schema: COVERAGE_REPORT_SCHEMA,
      tool,
      sources: Array.from(this.sources.values()),
      units: this.units,
      nodes: Array.from(this.nodes.values()),
    };
  }
}

/**
 * Convert parsed Dafny assertion batches into a coverage report.
 *
 * Each run of consecutive batches with the same method and kind becomes one
 * unit (Dafny prints one `Results for X (kind)` block per method), so report
 * order matches log order.
 */
export function dafnyBatchesToReport(batches: readonly ParsedBatch[], info: DafnyReportInfo = {}): CoverageReport {
  const builder = new ReportBuilder();
  let unit: ReportUnit | undefined;

  for (const batch of batches) {
    if (!unit || unit.name !== batch.methodName || unit.kind !== batch.methodType) {
      unit = { id: `u${builder.units.length}`, name: batch.methodName, kind: batch.methodType, queries: [] };
      builder.units.push(unit);
    }

    // Node creation order mirrors the log: top, then each dependency (and its
    // callee clause), then each unused fact.
    const goal = builder.node(batch.topAssertion);
    const used = batch.provedBy.map((p) => builder.node(p));
    const unused = batch.unusedBy.map((p) => builder.node(p));

    unit.queries.push({
      id: `${unit.id}q${unit.queries.length}`,
      index: batch.batchIndex,
      outcome: batch.outcome,
      ...(batch.durationMs !== undefined ? { durationMs: batch.durationMs } : {}),
      resourceCount: batch.resourceCount,
      goals: [goal],
      used,
      unused,
    });
  }

  return builder.build(info);
}
