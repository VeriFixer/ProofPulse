export { CovStatus, TokenType } from "./types.js";
export type { SourceLocation, NodeData } from "./types.js";
export { ProofNode } from "./proof-node.js";
export type { Roles, TopMeta } from "./proof-node.js";
export { ProofGraph, formatDuration } from "./proof-graph.js";
export { Proof, parseProof, analyzeReport } from "./proof.js";
export { tokenTypeForKinds, nodeKindForTokenType } from "./node-kind.js";
export { applyCoverage, applyCoverageInternal, applyCoverageSemantic, computeLineStatus, getNodesByLine } from "./coverage.js";
export { serializeProofGraph, deserializeProofGraph } from "./serialization.js";
export { generateSpansFragment, getDependsOn, getProvedBy, getProves } from "./rendering.js";
export { generateTextReport } from "./report.js";
export type { ReportOptions } from "./report.js";
export { buildSpanTree, computeSpanTreeLineStatus, computeLineStatusFromTree, minStatus, maxStatus } from "./span-tree.js";
export type { SpanNode } from "./span-tree.js";

// Coverage report format (proofpulse-coverage/v1)
export {
  COVERAGE_REPORT_SCHEMA,
  VerifierId,
  SolverKind,
  UnitKind,
  QueryOutcome,
  NodeKind,
  PROOF_UNIT_KINDS,
  isCallKind,
} from "./report/coverage-report.js";
export type {
  CoverageReport,
  ReportNode,
  ReportQuery,
  ReportUnit,
  ReportSource,
  ReportSpan,
  ReportPosition,
  ReportTool,
} from "./report/coverage-report.js";
export { validateCoverageReport, ReportValidationError } from "./report/validate.js";
export { parseCoverageReport, serializeCoverageReport, reportFormatForPath, ReportFormat } from "./report/io.js";

// Verifier backends
export { RunStatus, SourceLanguage } from "./backends/backend.js";
export type {
  VerifierBackend,
  BackendRun,
  BackendOptions,
  BackendCapabilities,
  BackendSpecificOptions,
  DafnySpecificOptions,
  SolverConfig,
  MinimizationConfig,
  MinimizerCommand,
  MinimizationHook,
  SolverMinimizer,
  ToolInfo,
} from "./backends/backend.js";
export { BackendRegistry, createDefaultRegistry } from "./backends/registry.js";
export { Z3Minimizer, Z3WrapperEnv } from "./minimization/z3-minimizer.js";
export { assertNever } from "./util/assert-never.js";

// Dafny backend
export { DafnyBackend, dafnyRunToBackendRun } from "./backends/dafny/backend.js";
export { DafnyMinimizationHook } from "./backends/dafny/minimization-hook.js";
export {
  runDafny,
  resolveDafnyPathWithSource,
  resolveZ3PathWithSource,
  probeVersion,
  ResolveSource,
  DEFAULT_DAFNY_COMMAND,
} from "./backends/dafny/runner.js";
export type { ResolvedPath, DafnyRunResult, DafnyRunOptions } from "./backends/dafny/runner.js";
export { DafnyReportParser, dafnyLogToReport } from "./backends/dafny/log-parser.js";
export type { ParsedBatch } from "./backends/dafny/log-parser.js";
export { dafnyBatchesToReport } from "./backends/dafny/adapter.js";
export type { DafnyReportInfo } from "./backends/dafny/adapter.js";
export { classifyNodeType, dafnyMessageKind, DAFNY_MESSAGE_RULES } from "./backends/dafny/messages.js";
