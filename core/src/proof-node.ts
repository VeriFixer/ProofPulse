import { CovStatus, TokenType, SourceLocation, VacuityRole } from "./types.js";
import { NodeKind, QueryOutcome, UnitKind } from "./report/coverage-report.js";
import { tokenTypeForKinds } from "./node-kind.js";

export interface Roles {
  isTop: boolean;
  isCall: boolean;
  isProvedBy: boolean;
  isUnused: boolean;
}

export interface TopMeta {
  batchIndex: number;
  batchOutcome: QueryOutcome;
  batchDuration?: string;
  batchResourceCount?: number;
}

export class ProofNode {
  readonly file: string;
  readonly start: SourceLocation;
  readonly end: SourceLocation;
  readonly methodName: string;
  readonly methodType: UnitKind;
  readonly locationId: string;

  roles: Roles;
  /** Messages of every occurrence merged into this node, in order. */
  prooftexts: string[];
  /** Kind of each occurrence, parallel to `prooftexts`. */
  kinds: NodeKind[];
  topMeta?: TopMeta;
  provedBy: Set<ProofNode>;
  proofUnused: Set<ProofNode>;
  connections: Set<ProofNode>;

  covStatus: CovStatus;
  covStatusInternal: CovStatus;
  /** Set when the node takes part in a vacuous (or intentionally vacuous) proof. */
  vacuity?: VacuityRole;

  constructor(
    file: string,
    start: SourceLocation,
    end: SourceLocation,
    methodName: string,
    methodType: UnitKind,
    prooftext: string,
    kind: NodeKind,
  ) {
    this.file = file;
    this.start = start;
    this.end = end;
    this.methodName = methodName;
    this.methodType = methodType;
    this.prooftexts = [prooftext];
    this.kinds = [kind];

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
    return tokenTypeForKinds(this.kinds, this.roles.isTop);
  }

  get type(): TokenType {
    return this.getType();
  }

  addRole(role: keyof Roles): void {
    this.roles[role] = true;
  }

  addProoftext(text: string, kind: NodeKind): void {
    this.prooftexts.push(text);
    this.kinds.push(kind);
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
