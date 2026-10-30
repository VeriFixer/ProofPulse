import type { UnitKind } from "./report/coverage-report.js";

export enum CovStatus {
  CovComplete = "CovComplete",
  CovTest = "CovTest",
  Uncovered = "Uncovered",
  /** Proved, used or reached only through contradictory facts (see VacuityRole). */
  Vacuous = "Vacuous",
}

/** Why a node is Vacuous, or that its vacuous proof is intentional. */
export enum VacuityRole {
  /** Goal proved only from contradictory facts. */
  Goal = "goal",
  /** Fact in the contradiction behind a vacuous goal, and needed by no sound proof. */
  Cause = "cause",
  /** Seen only in vacuous proofs: unreachable under the contradiction. */
  Affected = "affected",
  /** Goal proved by contradiction on purpose; keeps its normal status. */
  Intentional = "intentional",
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
  Condition = "Condition",
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
  vacuity?: VacuityRole;
  methodName?: string;
  methodType?: UnitKind;
}
