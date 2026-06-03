export enum CovStatus {
  CovComplete = "CovComplete",
  CovTest = "CovTest",
  Uncovered = "Uncovered",
}

export enum TokenType {
  Undefined = "Undefined",
  Precondition = "Precondition",
  Postcondition = "Postcondition",
  AssertionManual = "AssertionManual",
  AssertionAutomatic = "AssertionAutomatic",
  LoopInvariant = "LoopInvariant",
  Call = "Call",
  CodeLine = "CodeLine",
}

export interface SourceLocation {
  line: number;
  col: number;
}

export interface NodeData {
  id: string;
  file: string;
  start: SourceLocation;
  end: SourceLocation;
  prooftexts: string[];
  roles: { isTop: boolean; isCall: boolean; isProvedBy: boolean; isUnused: boolean };
  type: TokenType;
  covStatus: CovStatus;
  covStatusInternal: CovStatus;
  methodName?: string;
  methodType?: string;
}

export interface DafnyResult {
  log: string;
  exitCode: number;
  timedOut?: boolean;
  error?: string;
}

export interface DafnyOptions {
  dafnyPath?: string;
  z3Path?: string;
  timeoutSeconds?: number;
  forceMinimization?: boolean;
  /** Disable Dafny's abstract interpretation pass (--no-abstract-interpretation). */
  noAbstractInterpretation?: boolean;
  /** Called with warning messages (e.g. potential version incompatibility). */
  onWarning?: (msg: string) => void;
}
