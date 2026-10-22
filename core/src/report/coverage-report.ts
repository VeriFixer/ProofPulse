/**
 * proofpulse-coverage/v1 — the language-neutral input to ProofPulse.
 *
 * A backend (Dafny today; Verus and Kani later) runs a verifier and produces a
 * CoverageReport: which facts each successful solver query used and did not
 * use. Everything after this point (proof graph, coverage, rendering) is
 * verifier-independent.
 *
 * The TypeScript types below are the file format: a report serializes to
 * YAML/JSON as-is, and enum members are stored as their string values.
 */

export const COVERAGE_REPORT_SCHEMA = "proofpulse-coverage/v1";

export enum VerifierId {
  Dafny = "dafny",
  Verus = "verus",
  Kani = "kani",
}

export enum SolverKind {
  Z3 = "z3",
  Cvc5 = "cvc5",
  Cbmc = "cbmc",
}

/** What a verification unit checks. */
export enum UnitKind {
  Correctness = "correctness",
  WellFormedness = "well-formedness",
  Termination = "termination",
  Harness = "harness",
  Other = "other",
}

/**
 * Solver result for one query. Values match the outcome names verifiers print
 * (Dafny/Boogie `ProverInterface.Outcome`), so existing graph YAML is unchanged.
 */
export enum QueryOutcome {
  Valid = "Valid",
  Invalid = "Invalid",
  TimeOut = "TimeOut",
  OutOfMemory = "OutOfMemory",
  OutOfResource = "OutOfResource",
  Undetermined = "Undetermined",
  Bounded = "Bounded",
  Error = "Error",
}

/** What a source element is, as far as the proof is concerned. */
export enum NodeKind {
  Precondition = "precondition",
  Postcondition = "postcondition",
  /** User-written assertion. */
  Assert = "assert",
  /** Check the verifier adds itself (bounds, null, termination, …). */
  ImplicitCheck = "implicit-check",
  Assume = "assume",
  Invariant = "invariant",
  /** Callee precondition at a call site. */
  CallRequires = "call-requires",
  /** Callee postcondition at a call site. */
  CallEnsures = "call-ensures",
  Axiom = "axiom",
  Lemma = "lemma",
  /** Ordinary code (assignments, statements). */
  Code = "code",
  Other = "other",
}

export interface ReportPosition {
  line: number;
  col: number;
}

export interface ReportSpan {
  /** Id of an entry in `CoverageReport.sources`. */
  file: string;
  start: ReportPosition;
  end: ReportPosition;
}

export interface ReportSource {
  id: string;
  /** Path as reported by the verifier. */
  path: string;
  /** Hex SHA-256 of the file content the report was produced from. */
  sha256?: string;
}

export interface ReportTool {
  name: VerifierId;
  version?: string;
  solver?: { kind: SolverKind; version?: string };
  /** Whether unsat cores were minimized. */
  minimized?: boolean;
}

export interface ReportNode {
  id: string;
  kind: NodeKind;
  span: ReportSpan;
  /** The verifier's description of the element, e.g. "this postcondition holds". */
  message: string;
  /** Source text of the element, when the backend knows it. */
  text?: string;
  /** Callee clauses this call-site node refers to (node ids). */
  callTargets?: string[];
}

export interface ReportQuery {
  id: string;
  /** Position of the query within its unit, as numbered by the verifier. */
  index: number;
  outcome: QueryOutcome;
  durationMs?: number;
  resourceCount?: number;
  /** Nodes this query proved / checked. */
  goals: string[];
  /** Nodes in the unsat core (needed by the proof). */
  used: string[];
  /** Tracked nodes not in the unsat core. */
  unused: string[];
}

export interface ReportUnit {
  id: string;
  name: string;
  kind: UnitKind;
  queries: ReportQuery[];
}

export interface CoverageReport {
  schema: typeof COVERAGE_REPORT_SCHEMA;
  tool: ReportTool;
  sources: ReportSource[];
  units: ReportUnit[];
  nodes: ReportNode[];
}

/** Unit kinds whose queries are proof obligations ProofPulse analyses. */
export const PROOF_UNIT_KINDS: ReadonlySet<UnitKind> = new Set([UnitKind.Correctness, UnitKind.Harness]);

export function isCallKind(kind: NodeKind): boolean {
  return kind === NodeKind.CallRequires || kind === NodeKind.CallEnsures;
}

export function enumValues<T extends Record<string, string>>(e: T): ReadonlySet<string> {
  return new Set(Object.values(e));
}
