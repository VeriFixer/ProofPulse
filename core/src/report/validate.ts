import {
  COVERAGE_REPORT_SCHEMA,
  CoverageReport,
  NodeKind,
  QueryOutcome,
  SolverKind,
  UnitKind,
  VerifierId,
  enumValues,
} from "./coverage-report.js";

export class ReportValidationError extends Error {
  /** JSON-pointer-like path of the offending value, e.g. "/units/0/queries/2/used/1". */
  readonly path: string;

  constructor(path: string, message: string) {
    super(`${path}: ${message}`);
    this.name = "ReportValidationError";
    this.path = path;
  }
}

const NODE_KINDS = enumValues(NodeKind);
const UNIT_KINDS = enumValues(UnitKind);
const OUTCOMES = enumValues(QueryOutcome);
const VERIFIERS = enumValues(VerifierId);
const SOLVERS = enumValues(SolverKind);

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function expectArray(v: unknown, path: string): unknown[] {
  if (!Array.isArray(v)) throw new ReportValidationError(path, "expected an array");
  return v;
}

function expectObject(v: unknown, path: string): Record<string, unknown> {
  if (!isObject(v)) throw new ReportValidationError(path, "expected an object");
  return v;
}

function expectString(v: unknown, path: string): string {
  if (typeof v !== "string") throw new ReportValidationError(path, "expected a string");
  return v;
}

function expectInt(v: unknown, path: string): number {
  if (typeof v !== "number" || !Number.isInteger(v)) throw new ReportValidationError(path, "expected an integer");
  return v;
}

function expectNumber(v: unknown, path: string): number {
  if (typeof v !== "number" || Number.isNaN(v)) throw new ReportValidationError(path, "expected a number");
  return v;
}

function expectEnum(v: unknown, values: ReadonlySet<string>, path: string): string {
  const s = expectString(v, path);
  if (!values.has(s)) throw new ReportValidationError(path, `unknown value "${s}"`);
  return s;
}

function expectPosition(v: unknown, path: string): void {
  const o = expectObject(v, path);
  expectInt(o.line, `${path}/line`);
  expectInt(o.col, `${path}/col`);
}

/**
 * Validate an untyped value (e.g. freshly parsed YAML/JSON) and return it as a
 * CoverageReport. Unknown node and unit kinds are rewritten to `Other` (forward
 * compatibility); everything else must be well-formed.
 */
export function validateCoverageReport(data: unknown): CoverageReport {
  const root = expectObject(data, "");
  if (root.schema !== COVERAGE_REPORT_SCHEMA) {
    throw new ReportValidationError(
      "/schema",
      `unsupported schema "${String(root.schema)}" — expected "${COVERAGE_REPORT_SCHEMA}". ` +
        "Upgrade ProofPulse or regenerate the report.",
    );
  }

  const tool = expectObject(root.tool, "/tool");
  expectEnum(tool.name, VERIFIERS, "/tool/name");
  if (tool.version !== undefined) expectString(tool.version, "/tool/version");
  if (tool.solver !== undefined) {
    const solver = expectObject(tool.solver, "/tool/solver");
    expectEnum(solver.kind, SOLVERS, "/tool/solver/kind");
  }

  const sourceIds = new Set<string>();
  expectArray(root.sources, "/sources").forEach((s, i) => {
    const src = expectObject(s, `/sources/${i}`);
    const id = expectString(src.id, `/sources/${i}/id`);
    expectString(src.path, `/sources/${i}/path`);
    if (sourceIds.has(id)) throw new ReportValidationError(`/sources/${i}/id`, `duplicate source id "${id}"`);
    sourceIds.add(id);
  });

  const nodeIds = new Set<string>();
  const nodes = expectArray(root.nodes, "/nodes");
  nodes.forEach((n, i) => {
    const p = `/nodes/${i}`;
    const node = expectObject(n, p);
    const id = expectString(node.id, `${p}/id`);
    if (nodeIds.has(id)) throw new ReportValidationError(`${p}/id`, `duplicate node id "${id}"`);
    nodeIds.add(id);
    const kind = expectString(node.kind, `${p}/kind`);
    if (!NODE_KINDS.has(kind)) node.kind = NodeKind.Other;
    const span = expectObject(node.span, `${p}/span`);
    const file = expectString(span.file, `${p}/span/file`);
    if (!sourceIds.has(file)) throw new ReportValidationError(`${p}/span/file`, `unknown source "${file}"`);
    expectPosition(span.start, `${p}/span/start`);
    expectPosition(span.end, `${p}/span/end`);
    expectString(node.message, `${p}/message`);
    if (node.text !== undefined) expectString(node.text, `${p}/text`);
  });

  // Second pass: call targets may reference nodes declared later.
  nodes.forEach((n, i) => {
    const node = n as Record<string, unknown>;
    if (node.callTargets === undefined) return;
    expectArray(node.callTargets, `/nodes/${i}/callTargets`).forEach((t, j) => {
      const ref = expectString(t, `/nodes/${i}/callTargets/${j}`);
      if (!nodeIds.has(ref)) throw new ReportValidationError(`/nodes/${i}/callTargets/${j}`, `unknown node "${ref}"`);
    });
  });

  const unitIds = new Set<string>();
  expectArray(root.units, "/units").forEach((u, i) => {
    const p = `/units/${i}`;
    const unit = expectObject(u, p);
    const id = expectString(unit.id, `${p}/id`);
    if (unitIds.has(id)) throw new ReportValidationError(`${p}/id`, `duplicate unit id "${id}"`);
    unitIds.add(id);
    expectString(unit.name, `${p}/name`);
    const kind = expectString(unit.kind, `${p}/kind`);
    if (!UNIT_KINDS.has(kind)) unit.kind = UnitKind.Other;

    expectArray(unit.queries, `${p}/queries`).forEach((q, j) => {
      const qp = `${p}/queries/${j}`;
      const query = expectObject(q, qp);
      expectString(query.id, `${qp}/id`);
      expectInt(query.index, `${qp}/index`);
      expectEnum(query.outcome, OUTCOMES, `${qp}/outcome`);
      if (query.durationMs !== undefined) expectNumber(query.durationMs, `${qp}/durationMs`);
      if (query.resourceCount !== undefined) expectInt(query.resourceCount, `${qp}/resourceCount`);

      const refs = (field: "goals" | "used" | "unused"): void => {
        expectArray(query[field], `${qp}/${field}`).forEach((r, k) => {
          const ref = expectString(r, `${qp}/${field}/${k}`);
          if (!nodeIds.has(ref)) throw new ReportValidationError(`${qp}/${field}/${k}`, `unknown node "${ref}"`);
        });
      };
      // A fact may appear in both `used` and `unused` of one query: Dafny
      // reports the same location+message in both lists when it occurs at
      // several places in the VC. The graph merges them, so no disjointness check.
      refs("goals");
      refs("used");
      refs("unused");
    });
  });

  return root as unknown as CoverageReport;
}
