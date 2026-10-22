import type { UnitKind } from "./report/coverage-report.js";

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
  Assume = "Assume",
  Axiom = "Axiom",
  Lemma = "Lemma",
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
  methodType?: UnitKind;
}
