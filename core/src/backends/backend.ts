/**
 * Verifier backends: one per verifier (Dafny today). A backend runs its
 * verifier and returns a language-neutral CoverageReport.
 */
import type { CoverageReport } from "../report/coverage-report.js";
import { SolverKind, VerifierId } from "../report/coverage-report.js";

export { SolverKind, VerifierId };

/** VS Code language ids of the source languages ProofPulse handles. */
export enum SourceLanguage {
  Dafny = "dafny",
  Rust = "rust",
}

export enum RunStatus {
  Completed = "completed",
  TimedOut = "timedOut",
  Aborted = "aborted",
  Failed = "failed",
}

export interface ToolInfo {
  path: string;
  version?: string;
}

export interface BackendRun {
  status: RunStatus;
  /** Present when Completed. */
  report?: CoverageReport;
  /** The verifier's native output (e.g. Dafny's text log), for debugging. */
  rawLog?: string;
  exitCode: number;
  /** Human-readable detail for Failed (and diagnostics for TimedOut). */
  errorMessage?: string;
}

export interface BackendCapabilities {
  /** Reports used/unused facts per goal. */
  proofDependencies: boolean;
  /** Links call-site clauses to the callee clauses they refer to. */
  callTargets: boolean;
  /** Can report a preliminary (unminimized) result before the final one. */
  progressive: boolean;
}

export interface SolverConfig {
  kind: SolverKind;
  /** Binary to run; resolved by the backend when absent. */
  path?: string;
}

export interface MinimizationConfig {
  /** Solver the minimizer forwards to. Defaults to the backend's own solver. */
  solver?: SolverConfig;
  /** Where the minimizer writes its log; defaults to a file in the run's temp dir. */
  logFile?: string;
}

/** Options only the Dafny backend understands. */
export interface DafnySpecificOptions {
  backend: VerifierId.Dafny;
  /** Pass --no-abstract-interpretation. */
  noAbstractInterpretation?: boolean;
  /** Pass --cores: how many solver processes Dafny runs in parallel. */
  cores?: number;
}

export type BackendSpecificOptions = DafnySpecificOptions;

export interface BackendOptions {
  /** Verifier executable; resolved by the backend when absent. */
  toolPath?: string;
  /** Solver the verifier runs with; the verifier's default when absent. */
  solver?: SolverConfig;
  /** Minimize unsat cores; absent = no minimization. */
  minimization?: MinimizationConfig;
  timeoutSeconds?: number;
  signal?: AbortSignal;
  onWarning?: (msg: string) => void;
  /** Called with the unminimized result before minimization starts (progressive backends). */
  onPreliminaryResult?: (run: BackendRun) => void;
  backendOptions?: BackendSpecificOptions;
}

/**
 * Command the verifier spawns instead of its real solver. The minimizer speaks
 * the solver's protocol, forwards to the real solver and minimizes unsat cores.
 */
export interface MinimizerCommand {
  executable: string;
  env: Record<string, string>;
  /** Description of the setup, for diagnostics. */
  debugInfo: string[];
}

/** Verifier-independent unsat-core minimizer for one solver kind. */
export interface SolverMinimizer {
  readonly solverKind: SolverKind;
  prepare(solverPath: string, logFile: string, tmpDir: string, log: (msg: string) => void): Promise<MinimizerCommand>;
}

/** How one verifier is told to run the minimizer in place of its solver. */
export interface MinimizationHook {
  readonly supportedSolvers: readonly SolverKind[];
  apply(cmd: MinimizerCommand): { args: string[]; env: Record<string, string> };
}

export interface VerifierBackend {
  readonly id: VerifierId;
  readonly displayName: string;
  readonly fileExtensions: readonly string[];
  readonly languages: readonly SourceLanguage[];
  readonly capabilities: BackendCapabilities;
  /** Absent when this verifier cannot run the minimizer. */
  readonly minimizationHook?: MinimizationHook;

  probe(opts?: BackendOptions): Promise<ToolInfo | undefined>;
  run(file: string, opts?: BackendOptions): Promise<BackendRun>;
}
