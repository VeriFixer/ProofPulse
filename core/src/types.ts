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
  prooftext: string;
  isTopAssertion: boolean;
  type: TokenType;
  covStatus: CovStatus;
  covStatusInternal: CovStatus;
}

export interface DafnyResult {
  log: string;
  exitCode: number;
  timedOut?: boolean;
  error?: string;
}

export interface DafnyOptions {
  dafnyPath?: string;
  timeoutSeconds?: number;
  forceMinimization?: boolean;
}
