import { CovStatus, TokenType, SourceLocation } from "./types.js";

export interface Roles {
  isTop: boolean;
  isCall: boolean;
  isProvedBy: boolean;
  isUnused: boolean;
}

export interface TopMeta {
  batchIndex: number;
  batchOutcome: string;
  batchDuration: string;
  batchResourceCount: number;
}

export class ProofNode {
  readonly file: string;
  readonly start: SourceLocation;
  readonly end: SourceLocation;
  readonly methodName: string;
  readonly methodType: string;
  readonly locationId: string;

  roles: Roles;
  prooftexts: string[];
  topMeta?: TopMeta;
  provedBy: Set<ProofNode>;
  proofUnused: Set<ProofNode>;
  connections: Set<ProofNode>;

  covStatus: CovStatus;
  covStatusInternal: CovStatus;

  constructor(
    file: string,
    start: SourceLocation,
    end: SourceLocation,
    methodName: string,
    methodType: string,
    prooftext: string,
  ) {
    this.file = file;
    this.start = start;
    this.end = end;
    this.methodName = methodName;
    this.methodType = methodType;
    this.prooftexts = [prooftext];

    this.roles = { isTop: false, isCall: false, isProvedBy: false, isUnused: false };
    this.provedBy = new Set();
    this.proofUnused = new Set();
    this.connections = new Set();
    this.covStatus = CovStatus.Uncovered;
    this.covStatusInternal = CovStatus.Uncovered;

    const normalize = (s: string) => s.replace(/\s+/g, " ").replace(/\|/g, "/").trim();
    const span = `${start.line},${start.col}-${end.line},${end.col}`;
    this.locationId = `${file}|${normalize(methodName)}|${normalize(methodType)}|${span}`;
  }

  getId(): string {
    return this.locationId;
  }

  getType(): TokenType {
    return classifyNodeType(this.prooftexts, this.roles.isTop);
  }

  get type(): TokenType {
    return this.getType();
  }

  addRole(role: keyof Roles): void {
    this.roles[role] = true;
  }

  addProoftext(text: string): void {
    this.prooftexts.push(text);
  }

  // Compatibility with old Node interface
  get isTopAssertion(): boolean {
    return this.roles.isTop;
  }

  get prooftext(): string {
    return this.prooftexts[0] ?? "";
  }

  get assertion_group(): string {
    return this.methodName;
  }

  getCovStatus(): CovStatus {
    return this.covStatus;
  }

  setCovStatus(s: CovStatus): void {
    this.covStatus = s;
  }

  getCovStatusInternal(): CovStatus {
    return this.covStatusInternal;
  }

  setCovStatusInternal(s: CovStatus): void {
    this.covStatusInternal = s;
  }
}

export function classifyNodeType(prooftexts: string[], isTopAssertion: boolean): TokenType {
  // If any prooftext indicates a call clause, classify as Call
  for (const prooftext of prooftexts) {
    if (prooftext.includes("ensures clause at") || prooftext.includes("requires clause at")) {
      return TokenType.Call;
    }
  }

  if (prooftexts.length === 0) {
    return TokenType.Undefined;
  }

  const prooftext = prooftexts[0];
  
  if (prooftext.includes("this postcondition holds")) {
    return TokenType.Postcondition;
  } else if (prooftext.includes("precondition always holds")) {
    return TokenType.Precondition;
  } else if (prooftext.includes("ensures clause at")) {
    return TokenType.Call;
  } else if (prooftext.includes("requires clause at")) {
    return TokenType.Call;
  } else if (prooftext.includes("ensures clause")) {
    return TokenType.Postcondition;
  } else if (prooftext.includes("requires clause")) {
    return TokenType.Precondition;
  } else if (prooftext.includes("assertion always holds")) {
    return TokenType.AssertionManual;
  } else if (
    prooftext.includes("loop invariant holds on entry") ||
    prooftext.includes("loop invariant is maintained by the loop") ||
    prooftext.includes("loop invariant always holds") ||
    prooftext === "loop invariant"
  ) {
    return TokenType.LoopInvariant;
  } else if (
    prooftext.includes("index in range") ||
    prooftext.includes("target object is never null") ||
    prooftext.includes("array is never null") ||
    prooftext.includes("which is subject to definite-assignment rules, is always initialized at this return point") ||
    prooftext.includes("which is subject to definite-assignment rules, is always initialized here") ||
    prooftext.includes("decreases expression is bounded below by") ||
    prooftext.includes("value always satisfies the subset constraints of") ||
    prooftext.includes("an array element is in the enclosing context's modifies clause") ||
    prooftext.includes("sufficient reads clause to read array element")
  ) {
    return TokenType.AssertionAutomatic;
  } else if (isTopAssertion) {
    return TokenType.AssertionAutomatic;
  } else {
    return TokenType.CodeLine;
  }
}
